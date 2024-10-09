// Copyright 2024 The Go Authors. All rights reserved.

// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// These benchmarks are based on the ones in github.com/google/btree.

package omap

import (
	"math/rand/v2"
	"sort"
	"testing"
)

const benchmarkTreeSize = 10_000

func BenchmarkInsert(b *testing.B) {
	b.StopTimer()
	insertP := rand.Perm(benchmarkTreeSize)
	b.StartTimer()
	i := 0
	for i < b.N {
		var m Map[int, int]
		for _, item := range insertP {
			m.Set(item, item)
			i++
			if i >= b.N {
				return
			}
		}
	}
}

func randMap(size int) (*Map[int, int], []int) {
	insertP := rand.Perm(size)
	var m Map[int, int]
	for _, item := range insertP {
		m.Set(item, item)
	}
	return &m, insertP
}

func newMap(els []int) *Map[int, int] {
	var m Map[int, int]
	for _, item := range els {
		m.Set(item, item)
	}
	return &m
}

// iterator setup
func BenchmarkSeek(b *testing.B) {
	b.StopTimer()
	size := 100_000
	m, _ := randMap(size)
	b.StartTimer()

	for i := 0; i < b.N; i++ {
		for range m.From(i % size).All() {
			break
		}
	}
}

func BenchmarkDeleteInsert(b *testing.B) {
	b.StopTimer()
	m, insertP := randMap(benchmarkTreeSize)
	b.StartTimer()
	for i := 0; i < b.N; i++ {
		m.Delete(insertP[i%benchmarkTreeSize])
		m.Set(insertP[i%benchmarkTreeSize], i)
	}
}
func BenchmarkDelete(b *testing.B) {
	b.StopTimer()
	insertP := rand.Perm(benchmarkTreeSize)
	removeP := rand.Perm(benchmarkTreeSize)
	b.StartTimer()
	i := 0
	for i < b.N {
		b.StopTimer()
		m := newMap(insertP)
		b.StartTimer()
		for _, item := range removeP {
			m.Delete(item)
			i++
			if i >= b.N {
				return
			}
		}
	}
}

func BenchmarkGet(b *testing.B) {
	b.StopTimer()
	insertP := rand.Perm(benchmarkTreeSize)
	removeP := rand.Perm(benchmarkTreeSize)
	b.StartTimer()
	i := 0
	for i < b.N {
		b.StopTimer()
		m := newMap(insertP)
		b.StartTimer()
		for _, item := range removeP {
			m.Get(item)
			i++
			if i >= b.N {
				return
			}
		}
	}
}

func BenchmarkAscend(b *testing.B) {
	arr := rand.Perm(benchmarkTreeSize)
	m := newMap(arr)
	sort.Ints(arr)
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		j := 0
		for k := range m.All() {
			if k != arr[j] {
				b.Fatalf("mismatch: expected: %v, got %v", arr[j], k)
			}
			j++
		}
	}
}
