# API

## Map

```
type Map[K, V any] struct{ ... }

func NewMap[K, V any](cmp func(K, K) int) *Map[K, V]

func (m *Map[K, V]) At(key K) V
func (m *Map[K, V]) Get(key K) (V, bool)
func (m *Map[K, V]) All() iter.Seq2[K, V]
func (m *Map[K, V]) Backward() iter.Seq2[K, V]
func (m *Map[K, V]) Clear()
func (m *Map[K, V]) Clone() *Map[K, V]
func (m *Map[K, V]) Delete(key K) bool
func (m *Map[K, V]) Index(key K) int
func (m *Map[K, V]) Insert(key K, val V) (old V, added bool)
func (m *Map[K, V]) Len() int
func (m *Map[K, V]) Max() (K, V, bool)
func (m *Map[K, V]) Min() (K, V, bool)
func (m *Map[K, V]) Nth(i int) (K, V)

func (m *Map[K, V]) Above(lo K) Range[K, V]
func (m *Map[K, V]) Below(hi K) Range[K, V]
func (m *Map[K, V]) From(lo K) Range[K, V]
func (m *Map[K, V]) To(hi K) Range[K, V]
```

## Range

```
type Range[K, V any] struct{ ... }

func (r Range[K, V]) All() iter.Seq2[K, V]
func (r Range[K, V]) Backward() iter.Seq2[K, V]
func (r Range[K, V]) Clear()
func (r Range[K, V]) Clone() *Map[K, V]
func (r Range[K, V]) Index(key K) int
func (r Range[K, V]) Len() int
func (r Range[K, V]) Max() (K, V, bool)
func (r Range[K, V]) Min() (K, V, bool)
func (r Range[K, V]) Nth(i int) (K, V)

func (r Range[K, V]) Below(hi K) Range[K, V]
func (r Range[K, V]) To(hi K) Range[K, V]
```

## OrderedMap

```
type OrderedMap[K cmp.Ordered, V any] struct{ ... }

func (m *OrderedMap[K, V]) All() iter.Seq2[K, V]
func (m *OrderedMap[K, V]) At(key K) V
func (m *OrderedMap[K, V]) Backward() iter.Seq2[K, V]
func (m *OrderedMap[K, V]) Clear()
func (m *OrderedMap[K, V]) Clone() *OrderedMap[K, V]
func (m *OrderedMap[K, V]) Delete(key K) bool
func (m *OrderedMap[K, V]) Get(key K) (V, bool)
func (m *OrderedMap[K, V]) Index(key K) int
func (m *OrderedMap[K, V]) Insert(key K, val V) (old V, added bool)
func (m *OrderedMap[K, V]) Len() int
func (m *OrderedMap[K, V]) Max() (K, V, bool)
func (m *OrderedMap[K, V]) Min() (K, V, bool)
func (m *OrderedMap[K, V]) Nth(i int) (K, V)

func (m *OrderedMap[K, V]) Above(lo K) OrderedRange[K, V]
func (m *OrderedMap[K, V]) Below(hi K) OrderedRange[K, V]
func (m *OrderedMap[K, V]) From(lo K) OrderedRange[K, V]
func (m *OrderedMap[K, V]) To(hi K) OrderedRange[K, V]
```

## OrderedRange

```
type OrderedRange[K cmp.Ordered, V any] struct{ ... }

func (r OrderedRange[K, V]) All() iter.Seq2[K, V]
func (r OrderedRange[K, V]) Backward() iter.Seq2[K, V]
func (r OrderedRange[K, V]) Clear()
func (r OrderedRange[K, V]) Clone() *OrderedMap[K, V]
func (r OrderedRange[K, V]) Index(key K) int
func (r OrderedRange[K, V]) Len() int
func (r OrderedRange[K, V]) Max() (K, V, bool)
func (r OrderedRange[K, V]) Min() (K, V, bool)
func (r OrderedRange[K, V]) Nth(i int) (K, V)

func (r OrderedRange[K, V]) Below(hi K) OrderedRange[K, V]
func (r OrderedRange[K, V]) To(hi K) OrderedRange[K, V]
```

