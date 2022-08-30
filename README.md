iter-group
==========

A trivial library to extend `(key, value)` iterators with a method
that returns a mapping type whose keys are grouped into some
collection of type `value`.

Essentially, it replaces this:

```
let a = [(1, 'a'), (2, 'b'), (3, 'c'), (2, 'd'), (1, 'e'), (1, 'f')];
let mut map: HashMap<_, Vec<_>> = HashMap::default();
for (k, v) in a.into_iter() {
    map.entry(k).or_default().push(v);
}

```

with this:

```
use iter_group:::IntoGroup;
let a = [(1, 'a'), (2, 'b'), (3, 'c'), (2, 'd'), (1, 'e'), (1, 'f')];
let map = a.into_iter().group::<HashMap<_, Vec<_>>>();
```

See the documentation for additional examples.
