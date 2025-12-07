#![cfg_attr(not(test), no_std)]

use core::cell::UnsafeCell;
use core::sync::atomic::Ordering;
use core::sync::atomic::compiler_fence;

use portable_atomic::{AtomicU8, AtomicUsize};

const READER_TAKEN: u8 = 0b10;
const WRITER_TAKEN: u8 = 0b01;

/// A lock-free circular bit buffer with seperatable read/write handles, and the ability
/// to align data for more efficient processing.
///
/// This buffer tracks whether a read or write handle exists, allowing the ability to
/// safely get a read or write handle at any time, or to split the struct into specific
/// handles.
pub struct BitBuffer<const N: usize> {
    data: UnsafeCell<[u8; N]>,

    read_pos: AtomicUsize,
    write_pos: AtomicUsize,

    handle_flags: AtomicU8,
}

impl<const N: usize> BitBuffer<N> {
    pub const fn new() -> Self {
        Self {
            data: UnsafeCell::new([0u8; N]),

            read_pos: AtomicUsize::new(0),
            write_pos: AtomicUsize::new(0),

            handle_flags: AtomicU8::new(0),
        }
    }

    pub fn try_writer(&self) -> Option<BitWriter<'_, N>> {
        let current_flags = self.handle_flags.load(Ordering::Acquire);

        if current_flags & WRITER_TAKEN != 0 {
            return None;
        }

        match self.handle_flags.compare_exchange(
            current_flags,
            current_flags | WRITER_TAKEN,
            Ordering::Acquire,
            Ordering::Relaxed,
        ) {
            Ok(_) => Some(BitWriter { buffer: self }),
            Err(_) => None,
        }
    }

    pub fn try_reader(&self) -> Option<BitReader<'_, N>> {
        let current_flags = self.handle_flags.load(Ordering::Acquire);

        if current_flags & READER_TAKEN != 0 {
            return None;
        }

        match self.handle_flags.compare_exchange(
            current_flags,
            current_flags | READER_TAKEN,
            Ordering::Acquire,
            Ordering::Relaxed,
        ) {
            Ok(_) => Some(BitReader { buffer: self }),
            Err(_) => None,
        }
    }

    pub fn try_split(&self) -> Option<(BitReader<'_, N>, BitWriter<'_, N>)> {
        let reader = self.try_reader();
        let writer = self.try_writer();

        reader.zip(writer)
    }

    pub fn is_writer_taken(&self) -> bool {
        self.handle_flags.load(Ordering::Acquire) & WRITER_TAKEN != 0
    }

    pub fn is_reader_taken(&self) -> bool {
        self.handle_flags.load(Ordering::Acquire) & READER_TAKEN != 0
    }

    /// Returns the number of bits that can be written to this buffer before it is full
    pub fn available_write_bits(&self) -> usize {
        let read_pos = self.read_pos.load(Ordering::Acquire);
        let write_pos = self.write_pos.load(Ordering::Acquire);

        let raw_capacity_bits = N * 8;

        let used_bits = if write_pos >= read_pos {
            write_pos - read_pos
        } else {
            raw_capacity_bits - read_pos + write_pos
        };

        // Reserve a single bit to tell whether the buffer is full or not
        raw_capacity_bits.saturating_sub(used_bits + 1)
    }

    pub fn available_read_bits(&self) -> usize {
        let read_pos = self.read_pos.load(Ordering::Acquire);
        let write_pos = self.write_pos.load(Ordering::Acquire);

        if write_pos >= read_pos {
            write_pos - read_pos
        } else {
            (N * 8) - read_pos + write_pos
        }
    }

    pub fn is_full(&self) -> bool {
        self.available_write_bits() == 0
    }

    #[inline(always)]
    pub fn is_writer_aligned(&self) -> bool {
        self.write_pos.load(Ordering::Acquire) % 8 == 0
    }

    #[inline(always)]
    pub fn is_reader_aligned(&self) -> bool {
        self.read_pos.load(Ordering::Acquire) % 8 == 0
    }

    #[allow(dead_code)]
    fn get_buf(&self) -> &'_ [u8; N] {
        unsafe { &*self.data.get() }
    }
}

pub struct BitReader<'a, const N: usize> {
    buffer: &'a BitBuffer<N>,
}

impl<'a, const N: usize> BitReader<'a, N> {
    pub fn read_bit(&mut self) -> Option<bool> {
        let read_pos = self.buffer.read_pos.load(Ordering::Acquire);
        let write_pos = self.buffer.write_pos.load(Ordering::Acquire);

        if read_pos == write_pos {
            return None;
        }

        let byte_idx = (read_pos / 8) % N;
        let bit_idx = read_pos % 8;

        let data = self.buffer.get_buf();
        let bit = (data[byte_idx] >> bit_idx) & 1;

        self.buffer
            .read_pos
            .store((read_pos + 1) % (N * 8), Ordering::Release);

        Some(bit != 0)
    }

    pub fn read_bits(&mut self, num_bits: u8) -> Option<u8> {
        // TODO Add a fast-path when `num_bits` is 8
        if num_bits > 8 {
            panic!("Number of bits to be read is greater than 8");
        }

        if self.buffer.available_read_bits() < num_bits as usize {
            return None;
        }

        let mut output = 0;

        for i in 0..num_bits {
            if let Some(bit) = self.read_bit() {
                if bit {
                    output |= 1 << i;
                }
            } else {
                return None;
            }
        }

        Some(output)
    }

    /// Attemps to read a byte.
    ///
    /// This is more efficient if [`BitBuffer::is_reader_aligned`] is true
    pub fn read_byte(&mut self) -> Option<u8> {
        let read_pos = self.buffer.read_pos.load(Ordering::Acquire);

        // Fast path: The code is aligned, therefore we do not need to iterate 8 bits
        if read_pos % 8 == 0 && self.buffer.available_read_bits() >= 8 {
            let byte_idx = (read_pos / 8) % N;
            let byte = self.buffer.get_buf()[byte_idx];

            self.buffer
                .read_pos
                .store((read_pos + 8) % (N * 8), Ordering::Release);
            Some(byte)
        } else {
            self.read_bits(8)
        }
    }

    pub fn read_bytes(&mut self, buf: &mut [u8]) -> Option<()> {
        if self.buffer.available_read_bits() < buf.len() * 8 {
            return None;
        }

        let read_pos = self.buffer.read_pos.load(Ordering::Acquire);

        // FAST PATH: We are aligned, and can read bytes rather than bits.
        // We are also able to minimize the atomic operations used.
        if read_pos % 8 == 0 {
            let data = self.buffer.get_buf();
            let bytes_to_read = buf.len();
            let start_byte = (read_pos / 8) % N;

            // Handle wrapping in the circular buffer
            let bytes_until_wrap = N - start_byte;

            if bytes_to_read <= bytes_until_wrap {
                // Contiguous chunk, no wrapping
                buf[..bytes_to_read].copy_from_slice(&data[start_byte..start_byte + bytes_to_read]);
            } else {
                // Non-contiguous memory, need to copy twice
                let first_part = bytes_until_wrap;
                let second_part = bytes_to_read - first_part;

                buf[..first_part].copy_from_slice(&data[start_byte..]);
                buf[first_part..bytes_to_read].copy_from_slice(&data[..second_part]);
            }

            self.buffer
                .read_pos
                .store((read_pos + bytes_to_read * 8) % (N * 8), Ordering::Release);
        } else {
            for byte in buf.iter_mut() {
                *byte = self
                    .read_byte()
                    .expect("Failed to get byte when we already checked the length!");
            }
        }

        Some(())
    }

    pub fn read_array<const M: usize>(&mut self) -> Option<[u8; M]> {
        let mut array = [0u8; M];

        self.read_bytes(&mut array).map(|_| array)
    }

    /// Hint to the internal structure that we will be doing a lot of reading, and
    /// therefore would like the reader to be aligned.
    ///
    /// This will be unable to align if the writer is currently pointing at the same
    /// beginning bit as the reader.
    ///
    /// This function is intended to optimize parsing when the input data is not all
    /// available at once. For example, reading data from an input stream, we can
    /// align the data early on to make the writes be aligned to the reader, making
    /// it possible to read entire bytes at once.
    ///
    /// # Returns
    /// The function will return whether the data is aligned or not
    pub fn hint_align(&mut self) -> bool {
        if self.buffer.is_reader_aligned() {
            return true;
        }

        // TODO Implement hint_align
        return false;
    }
}

impl<'a, const N: usize> Drop for BitReader<'a, N> {
    fn drop(&mut self) {
        self.buffer
            .handle_flags
            .and(!READER_TAKEN, Ordering::Release);
    }
}

pub struct BitWriter<'a, const N: usize> {
    buffer: &'a BitBuffer<N>,
}

impl<'a, const N: usize> BitWriter<'a, N> {
    pub fn write_bit(&mut self, bit: bool) -> Option<()> {
        if self.buffer.is_full() {
            return None;
        }

        let write_pos = self.buffer.write_pos.load(Ordering::Acquire);

        let byte_idx = (write_pos / 8) % N;
        let bit_idx = write_pos % 8;

        let data = unsafe { &mut *self.buffer.data.get() };

        if bit {
            data[byte_idx] |= 1 << bit_idx;
        } else {
            data[byte_idx] &= !(1 << bit_idx);
        }

        compiler_fence(Ordering::Release);

        self.buffer
            .write_pos
            .store((write_pos + 1) % (N * 8), Ordering::Release);

        Some(())
    }

    /// Writes the specified number of bits from the provided byte, starting with the LSB
    ///
    /// # Example
    /// ```rust
    /// # use alignable_bb::BitBuffer;
    /// let buffer = BitBuffer::<2>::new();
    /// let (mut reader, mut writer) = buffer.try_split().unwrap();
    ///
    /// writer.write_bits(0b101, 3);
    ///
    /// assert_eq!(reader.read_bits(3), Some(0b101));
    /// # assert_eq!(reader.read_bit(), None);
    /// ```
    pub fn write_bits(&mut self, byte: u8, bits: u8) -> Option<()> {
        assert!(bits <= 8, "a byte can only hold 8 bits");

        // Error if we are unable to return the requested number of bits
        if self.buffer.available_write_bits() < bits as usize {
            return None;
        }

        for i in 0..bits {
            let value = ((byte >> i) & 1) != 0;
            self.write_bit(value);
        }

        Some(())
    }

    /// Writes a byte, LSB-first
    pub fn write_byte(&mut self, byte: u8) -> Option<()> {
        if self.buffer.available_write_bits() < 8 {
            return None;
        }

        for i in 0..8 {
            // We know that we are able to write 8 bits, and there is only one writer, so a race condition should not be possible.
            self.write_bit((byte >> i) & 1 != 0)
                .expect("Race condition occured, unable to write byte!");
        }

        Some(())
    }

    pub fn write_bytes(&mut self, bytes: &[u8]) -> Option<()> {
        if self.buffer.available_write_bits() < 8 * bytes.len() {
            return None;
        }

        for &byte in bytes {
            self.write_byte(byte)
                .expect("Failed to write byte when we already checked for available size!");
        }

        Some(())
    }
}

impl<'a, const N: usize> Drop for BitWriter<'a, N> {
    fn drop(&mut self) {
        self.buffer
            .handle_flags
            .and(!WRITER_TAKEN, Ordering::Release);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_8_bits() {
        let buf = BitBuffer::<2>::new();
        let mut writer = buf.try_writer().unwrap();

        writer.write_bit(true);
        writer.write_bit(false);
        writer.write_bit(true);
        writer.write_bit(false);
        writer.write_bit(true);
        writer.write_bit(false);
        writer.write_bit(true);
        writer.write_bit(false);

        assert_eq!(buf.get_buf(), &[0b01010101, 0]);
        assert_eq!(buf.available_write_bits(), 7); // 1 less than total
        assert_eq!(buf.available_read_bits(), 8);
        assert!(!buf.is_full());
    }

    #[test]
    fn read_bit() {
        let mut buf = BitBuffer::<2>::new();
        buf.data = UnsafeCell::new([0b00000010, 0]);
        buf.write_pos.store(2, Ordering::Relaxed);

        let mut reader = buf.try_reader().unwrap();

        assert_eq!(buf.available_read_bits(), 2);
        assert_eq!(reader.read_bit(), Some(false));
        assert_eq!(reader.read_bit(), Some(true));
        assert_eq!(reader.read_bit(), None);
    }

    #[test]
    fn read_bits_unaligned() {
        let buf = BitBuffer::<32>::new();
        let (mut reader, mut writer) = buf.try_split().unwrap();

        writer.write_bit(false);
        writer.write_byte(0xFF);

        assert_eq!(reader.read_byte(), Some(0b11111110));
        assert_eq!(reader.read_byte(), None);
        assert_eq!(reader.read_bit(), Some(true));
        assert_eq!(reader.read_bit(), None);
    }

    #[test]
    fn write_out_of_space() {
        let buf = BitBuffer::<0>::new();
        let mut writer = buf.try_writer().unwrap();

        assert_eq!(writer.write_bit(true), None);
    }

    #[test]
    fn is_full() {
        let buf = BitBuffer::<1>::new();
        let mut writer = buf.try_writer().unwrap();

        for _ in 0..7 {
            writer.write_bit(true);
        }

        assert!(buf.is_full());
        assert_eq!(buf.available_write_bits(), 0);
        assert_eq!(buf.available_read_bits(), 7);
    }

    #[test]
    fn available_capacity() {
        assert_eq!(BitBuffer::<0>::new().available_write_bits(), 0 * 8);
        assert_eq!(BitBuffer::<3>::new().available_write_bits(), 3 * 8 - 1);
        assert_eq!(BitBuffer::<16>::new().available_write_bits(), 16 * 8 - 1);
        assert_eq!(BitBuffer::<32>::new().available_write_bits(), 32 * 8 - 1);
    }

    #[test]
    fn is_writer_aligned() {
        let buf = BitBuffer::<32>::new();
        let mut writer = buf.try_writer().unwrap();

        assert!(buf.is_writer_aligned());

        writer.write_bit(true);

        assert!(!buf.is_writer_aligned());

        for _ in 0..7 {
            writer.write_bit(true);
        }

        assert!(buf.is_writer_aligned())
    }
}
