// Package rng provides ranges: representations of sequences of ordered values.
package rng

import (
	"fmt"
	"strings"
)

// Range is a range of values of type K.
// K need not be ordered; that is, it is not constrained by [cmp.Ordered].
// It is up to the user to assign an ordering; Range simply represents
// the bounds of the range.
//
// The zero Range is an empty range.
type Range[T any] struct {
	lo, hi         T
	inclLo, inclHi bool
	infLo, infHi   bool
	rev            bool
}

func (r Range[T]) String() string {
	var b strings.Builder
	if r.infLo {
		b.WriteString("(-∞")
	} else {
		if r.inclLo {
			b.WriteByte('[')
		} else {
			b.WriteByte('(')
		}
		fmt.Fprint(&b, r.lo)
	}
	b.WriteString(", ")
	if r.infHi {
		b.WriteString("∞)")
	} else {
		fmt.Fprint(&b, r.hi)
		if r.inclHi {
			b.WriteByte(']')
		} else {
			b.WriteByte(')')
		}
	}
	if r.rev {
		b.WriteString(" backwards")
	}
	return b.String()
}

func (r Range[T]) IsBackwards() bool { return r.rev }

func (r Range[T]) Low() (v T, infinite, includes bool) {
	return r.lo, r.infLo, r.inclLo
}

func (r Range[T]) High() (v T, infinite, includes bool) {
	return r.hi, r.infHi, r.inclHi
}

// [t, inf)
func From[T any](t T) Range[T] {
	return Range[T]{lo: t, inclLo: true, infHi: true}
}

// (t, inf)
func Above[T any](t T) Range[T] {
	return Range[T]{lo: t, inclLo: false, infHi: true}
}

// ..., t)
func (r Range[T]) Below(t T) Range[T] {
	if !r.infHi {
		panic("uninitialized Range")
	}
	r.hi = t
	r.infHi = false
	r.inclHi = false
	return r
}

// ..., t]
func (r Range[T]) To(t T) Range[T] {
	if !r.infHi {
		panic("uninitialized Range")
	}
	r.hi = t
	r.infHi = false
	r.inclHi = true
	return r
}

func (r Range[T]) Backwards() Range[T] {
	r.rev = true
	return r
}
