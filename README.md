# Ordered Maps

This package provides ordered maps.
It is a fork of [github.com/rsc/omap](https://github.com/rsc/omap),
whose import path is rsc.io/omap.

An ordered map is an association between keys and values, where only comparisons
are permitted between keys.
Like standard Go maps, ordered maps support efficient access to keys and values.
Unlike standard Go maps, they support iteration in
key order, in both directions, for both the entire map and any subsequence of keys.

In this implementation, it takes logarithmic time (O(log _n_), where _n_ is the number
of keys in the map) to retrieve a value
from a key, set a key to a value, or delete a key and its associated value. It also
takes logarithmic time to retrieve the minimum or maximum key, or delete a subsequence
of keys and their values. In the absence of modifications, the time to iterate over
_k_ keys is O(_k_).
All these times are asymptotically optimal for data structures that allow only
comparison of keys.

## Ranges

This implementation supports iteration over, and deletion of, subsequences
via _ranges_. A `Range` consists of an underlying map and up to two bounds
specifying the Range's endpoints. Ranges are constructed with a natural API.
To iterate over all keys in a map `m` between `a` and `b` inclusive, write
```
for k, v := range m.From(a).To(b).All() {...}
```
To delete all keys in the map between `a` and `b`, but not including either
of those keys, write
```
m.Above(a).Below(b).Clear()
```
The range API supports subsequence operations for any contiguous subsequence 
of keys.

## Iteration guarantees

When modifications to a map are interleaved with iteration, this implementation
guarantees that each key provided by the iterator is the successor of the previous
key at the time that the `yield` function is called. That is, the iteration will
skip deleted keys that it has not yet encountered, and will included inserted
keys that are greater than its current key.

An iterator may required extra time to achieve this guarantee. In the worst case,
an iterator can take O(_klogn_) time to iterate over _k_ keys in a map of size _n_.
The extra time is only needed if the map is modified; if not, the iterator
runs in the optimal O(_k_) time.



 




