package rng

import (
	"slices"
	"testing"
)

const (
	min = -1
	max = 11
)

func Test(t *testing.T) {
	for _, test := range []struct {
		r    Range[int]
		want []int
	}{
		{Range[int]{}, nil},
		{From(1).To(3), []int{1, 2, 3}},
		{From(3).Below(4), []int{3}},
		{Above(2).To(5), []int{3, 4, 5}},
		{Above(8).Below(10), []int{9}},
		{From(9).Below(8), nil},
	} {
		got := slice(test.r)
		if !slices.Equal(got, test.want) {
			t.Errorf("%s: got %v, want %v", test.r, got, test.want)
		}
		rb := test.r.Backwards()
		t.Log(rb)
		got = slice(rb)
		want := slices.Clone(test.want)
		slices.Reverse(want)
		if !slices.Equal(got, want) {
			t.Errorf("%s: got %v, want %v", rb, got, want)
		}
	}
}

func slice(r Range[int]) []int {
	lo, linf, lincl := r.Low()
	hi, hinf, hincl := r.High()
	if linf {
		lo = min
	} else if !lincl {
		lo++
	}
	if hinf {
		hi = max
	} else if !hincl {
		hi--
	}
	var ints []int
	if r.IsBackwards() {
		for i := hi; i >= lo; i-- {
			ints = append(ints, i)
		}

	} else {
		for i := lo; i <= hi; i++ {
			ints = append(ints, i)
		}
	}
	return ints
}
