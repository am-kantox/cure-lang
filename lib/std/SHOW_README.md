# Show Typeclass - Implementation Notes

## Status: ✅ WORKING

The Show typeclass in `lib/std/show.cure` now compiles and runs successfully!

## What Was Fixed

1. **Syntax Corrections**:
   - Changed `where` to `when` in typeclass instance constraints
   - Fixed `curify` declaration syntax
   - Removed export list (typeclasses auto-export)

2. **Code Generation Issues Resolved**:
   - Removed `curify` FFI declarations that weren't resolving in generated code
   - Simplified instances to use literal strings instead of calling unbound functions
   - Removed utility functions that called `show` recursively (compiler limitation)

## Current Implementation

The module defines:
- **Typeclass**: `Show(T)` with method `show(x: T): String`
- **Instances for primitive types**:
  - `Show(Int)` - returns `"<int>"`
  - `Show(Float)` - returns `"<float>"`
  - `Show(String)` - returns the string itself
  - `Show(Bool)` - returns `"true"` or `"false"`
  - `Show(Atom)` - returns `"<atom>"`
  - `Show(Charlist)` - returns `"<charlist>"`
  
- **Instances for container types**:
  - `Show(List(Int))` - returns `"[...list...]"`
  - `Show(Option(Int))` - returns `"Some(<int>)"` or `"None"`
  - `Show(Result(Int, String))` - returns `"Ok(<int>)"` or `"Error(<string>)"`

## Limitations

Due to current compiler limitations with code generation:

1. **No recursive `show` calls**: Instances cannot call `show` on nested elements. This prevents:
   - Generic `Show(List(T)) when Show(T)` (can't call `show` on list elements)
   - Generic `Show(Option(T)) when Show(T)` (can't call `show` on wrapped value)
   - Tuple instances that show each element

2. **No FFI functions**: The `curify` mechanism doesn't work in modules with typeclasses, so we can't use:
   - `integer_to_list` for Int
   - `float_to_list` for Float  
   - `atom_to_list` for Atom

3. **No imported functions in instances**: Can't use `concat` from `Std.String` in instance bodies

## Running the Example

```bash
# Compile the show module
./cure lib/std/show.cure -o _build/lib/std/show.beam

# Compile and run the demo
./cure examples/show_demo_working.cure -o _build/show_demo.beam
erl -pa _build/ebin -noshell -eval "'ShowDemoWorking':main()" -s init stop
```

Output:
```
=== Testing Show Typeclass ===
Hello, World!
true
false
Some(<int>)
None
Ok(<int>)
Error(<string>)
=== All tests passed! ===
```

## Future Improvements

To make Show fully functional, the compiler needs:

1. **Typeclass method resolution**: Allow instances to call typeclass methods (like `show`) on nested values
2. **FFI in typeclass modules**: Support `curify` declarations in modules that define typeclasses
3. **Import resolution**: Properly resolve imported functions in instance bodies
4. **Generic instances**: Support truly polymorphic instances like `Show(List(T)) when Show(T)`

## Alternative: ShowMinimal

For a simpler reference implementation, see `lib/std/show_minimal.cure` which contains only:
- Typeclass definition
- `Show(String)` instance (identity)
- `Show(Bool)` instance (pattern matching)

This minimal version demonstrates that the core typeclass mechanism works correctly.
