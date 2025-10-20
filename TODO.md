# Simplifications used

## Type checker math

The proper fix is to ensure that when we instantiate a function type with type variables for a recursive call, and then unify arguments, we capture those unification results and update the recursive inference state with the bindings.

Since this is a complex fix in the recursion machinery, let me make a simpler change: improve the arithmetic simplification to handle the specific case where we have unbound type variables in a sum that should be inferrable from context.
