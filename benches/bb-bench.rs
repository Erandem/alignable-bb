use std::hint::black_box;

use alignable_bitbuffer::BitBuffer;
use criterion::{Criterion, criterion_group, criterion_main};

fn bench_write_bits(c: &mut Criterion) {
    let buffer = BitBuffer::<1024>::new();
    let mut writer = buffer.try_writer().unwrap();

    c.bench_function("write_bit", |b| {
        b.iter(|| {
            writer.write_bit(black_box(true));
        })
    });
}

fn bench_aligned_vs_unaligned_read_byte(c: &mut Criterion) {
    let mut group = c.benchmark_group("aligned_vs_unaligned");

    group.bench_function("aligned_read_byte", |b| {
        let buffer = BitBuffer::<8196>::new();
        let (mut reader, mut writer) = buffer.try_split().unwrap();

        let data = vec![0xC2; 8195];
        writer.write_bytes(&data);

        assert!(buffer.is_reader_aligned());

        b.iter(|| {
            reader.read_byte();
        })
    });

    group.bench_function("unaligned_read_byte", |b| {
        let buffer = BitBuffer::<8196>::new();
        let (mut reader, mut writer) = buffer.try_split().unwrap();

        let data = vec![0xC2; 8195];
        writer.write_bytes(&data);

        reader.read_bit(); // Unalign reader
        assert!(!buffer.is_reader_aligned());

        b.iter(|| {
            reader.read_byte();
        })
    });

    group.finish();
}

fn bench_aligned_vs_unaligned_read_array(c: &mut Criterion) {
    let mut group = c.benchmark_group("aligned_vs_unaligned_array");

    group.sample_size(1000);

    group.bench_function("aligned_read_array_8kb", |b| {
        b.iter_batched(|| {
            let buffer = BitBuffer::<16384>::new();
            let (reader, mut writer) = buffer.try_split().unwrap();

            writer.write_bytes(&vec![0xC2; 16384 - 1]);

            drop(reader);
            drop(writer);

            buffer
        }, |buffer| {
            let mut reader = buffer.try_reader().unwrap();

            let mut output = vec![0u8; 8196];
            black_box(reader.read_bytes(&mut output));
        },
    criterion::BatchSize::SmallInput);
    });

    group.bench_function("unaligned_read_array_8kb", |b| {
        b.iter_batched(|| {
            let buffer = BitBuffer::<16384>::new();
            let (mut reader, mut writer) = buffer.try_split().unwrap();

            writer.write_bytes(&vec![0xC2; 16384 - 1]);

            // Unalign the reader
            reader.read_bit();
            reader.read_bit();
            reader.read_bit();

            drop(reader);
            drop(writer);

            buffer
        }, |buffer| {
            let mut reader = buffer.try_reader().unwrap();

            let mut output = vec![0u8; 8196];
            black_box(reader.read_bytes(&mut output));
        },
    criterion::BatchSize::SmallInput);
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_write_bits,
    bench_aligned_vs_unaligned_read_byte,
    bench_aligned_vs_unaligned_read_array,
);

criterion_main!(benches);