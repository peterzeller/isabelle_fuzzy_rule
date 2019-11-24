# Fuzzy Rule Method

This is a new method for Isabelle that is an alternative to the existing `rule` method.

It performs matching differently, making it more flexible in many  cases:

- Goal and used rule do not have to be unifiable. Additional schematic variables and equality constraints are inserted automatically.
- Facts can be given in any order.

See [fuzzyrule_examples.thy](fuzzyrule_examples.thy) for examples.