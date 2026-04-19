defmodule Cure.Types.Derive do
  @moduledoc """
  Automatic typeclass instance derivation for records and ADTs.

  Generates protocol method implementations from a type's structure:

  - **Show**: concatenates field names and `show()` of each field value
  - **Eq**: structural equality (all fields equal)
  - **Ord**: lexicographic comparison of fields
  - **Functor** (v0.21.0): generates `fmap(x, f)` that applies `f`
    to every field. Intended for single-parameter records like
    `rec Box(A)\n  value: A`.
  - **Monoid** (v0.21.0): generates `combine(a, b)` that pairwise
    combines each field with `<>`. Users supply `empty/0`
    separately; the derivation intentionally does not guess it.
  - **JSON** (v0.21.0): generates `to_json(x)` that renders the
    record as a JSON object whose keys are the field names (no
    escaping beyond what `show/1` would produce). `from_json/1` is
    reserved for a future release.

  ## Usage (from Cure source)

      rec Person
        name: String
        age: Int

      # Auto-derive Show for Person
      @derive(Show)

  ## Programmatic usage

      impls = Cure.Types.Derive.derive(:show, "Person", [:name, :age])
  """

  @doc """
  Generate protocol method implementation AST for a given typeclass.

  Returns a list of `{:function_def, meta, body}` AST nodes.
  """
  @spec derive(atom(), String.t(), [atom()]) :: [tuple()]
  def derive(:show, type_name, fields) do
    derive_show(type_name, fields)
  end

  def derive(:eq, type_name, fields) do
    derive_eq(type_name, fields)
  end

  def derive(:ord, _type_name, fields) do
    derive_ord(fields)
  end

  def derive(:functor, type_name, fields) do
    derive_functor(type_name, fields)
  end

  def derive(:monoid, type_name, fields) do
    derive_monoid(type_name, fields)
  end

  def derive(:json, type_name, fields) do
    derive_json(type_name, fields)
  end

  def derive(_typeclass, _type_name, _fields), do: []

  @doc """
  Check if a typeclass can be derived for a type.
  """
  @spec can_derive?(atom()) :: boolean()
  def can_derive?(:show), do: true
  def can_derive?(:eq), do: true
  def can_derive?(:ord), do: true
  def can_derive?(:functor), do: true
  def can_derive?(:monoid), do: true
  def can_derive?(:json), do: true
  def can_derive?(_), do: false

  # -- Show derivation ---------------------------------------------------------

  defp derive_show(type_name, fields) do
    # Generate: fn show(x: Type) -> String = "TypeName{field1: ..., field2: ...}"
    body =
      if fields == [] do
        {:literal, [subtype: :string], type_name}
      else
        # Build: "TypeName{" <> "field1: " <> show(x.f1) <> ", " <> ... <> "}"
        field_parts =
          fields
          |> Enum.map(fn field ->
            field_access =
              {:attribute_access, [attribute: Atom.to_string(field)], [{:variable, [scope: :local], "x"}]}

            show_call = {:function_call, [name: "show"], [field_access]}

            # "field_name: " <> show(x.field_name)
            concat(
              {:literal, [subtype: :string], "#{field}: "},
              show_call
            )
          end)
          |> Enum.intersperse({:literal, [subtype: :string], ", "})
          |> Enum.reduce(&concat(&2, &1))

        # "TypeName{" <> fields_str <> "}"
        concat(
          concat({:literal, [subtype: :string], "#{type_name}{"}, field_parts),
          {:literal, [subtype: :string], "}"}
        )
      end

    [
      {:function_def,
       [
         name: "show",
         params: [{:param, [type: {:variable, [], type_name}], "x"}],
         visibility: :public,
         arity: 1,
         line: 0
       ], [body]}
    ]
  end

  defp concat(left, right) do
    {:binary_op, [operator: :<>, category: :string], [left, right]}
  end

  # -- Eq derivation -----------------------------------------------------------

  defp derive_eq(_type_name, _fields) do
    # Generate: fn eq(a: Type, b: Type) -> Bool = a == b
    # Structural equality works for records (maps) in Erlang
    body =
      {:binary_op, [operator: :==, category: :comparison],
       [
         {:variable, [scope: :local], "a"},
         {:variable, [scope: :local], "b"}
       ]}

    [
      {:function_def,
       [
         name: "eq",
         params: [
           {:param, [], "a"},
           {:param, [], "b"}
         ],
         visibility: :public,
         arity: 2,
         line: 0
       ], [body]}
    ]
  end

  # -- Ord derivation ----------------------------------------------------------

  defp derive_ord(_fields) do
    # Generate comparison using Erlang's built-in term ordering
    # compare(a, b) = if a < b then :lt elif a > b then :gt else :eq
    body =
      {:conditional, [],
       [
         {:binary_op, [operator: :<, category: :comparison],
          [
            {:variable, [scope: :local], "a"},
            {:variable, [scope: :local], "b"}
          ]},
         {:literal, [subtype: :symbol], :lt},
         {:conditional, [],
          [
            {:binary_op, [operator: :>, category: :comparison],
             [
               {:variable, [scope: :local], "a"},
               {:variable, [scope: :local], "b"}
             ]},
            {:literal, [subtype: :symbol], :gt},
            {:literal, [subtype: :symbol], :eq}
          ]}
       ]}

    [
      {:function_def,
       [
         name: "compare",
         params: [
           {:param, [], "a"},
           {:param, [], "b"}
         ],
         visibility: :public,
         arity: 2,
         line: 0
       ], [body]}
    ]
  end

  # -- Functor derivation (v0.21.0) -------------------------------------------
  #
  # For `rec Box(A)\n  value: A`, generate:
  #
  #   fn fmap(x: Box, f) -> Box = Box{value: f(x.value)}
  #
  # For a multi-field record the same transformation is applied to every
  # field. Mathematically this is only a functor when every field has the
  # same type parameter, but pragmatically the generated `fmap` is useful
  # on any parameterised record and matches user expectations.
  defp derive_functor(type_name, fields) do
    pairs =
      Enum.map(fields, fn field ->
        field_str = Atom.to_string(field)
        field_access = {:attribute_access, [attribute: field_str], [{:variable, [scope: :local], "x"}]}
        applied = {:function_call, [name: "f"], [field_access]}
        {:pair, [], [{:literal, [subtype: :symbol], field}, applied]}
      end)

    body = {:function_call, [name: type_name, record: true], pairs}

    [
      {:function_def,
       [
         name: "fmap",
         params: [
           {:param, [type: {:variable, [], type_name}], "x"},
           {:param, [], "f"}
         ],
         visibility: :public,
         arity: 2,
         line: 0
       ], [body]}
    ]
  end

  # -- Monoid derivation (v0.21.0) --------------------------------------------
  #
  # Generates:
  #
  #   fn combine(a: Record, b: Record) -> Record =
  #     Record{field1: a.field1 <> b.field1, field2: a.field2 <> b.field2}
  #
  # `<>` is the Cure string/list concatenation operator, polymorphic by
  # value: strings concatenate as strings, lists as lists, bitstrings as
  # bitstrings. Primitive fields (Int/Float) require the user to provide
  # a custom `combine` override; this derivation does not attempt to
  # dispatch a type-specific combine function. Users wire up `empty/0`
  # separately -- the derivation intentionally does not guess a neutral
  # element.
  defp derive_monoid(type_name, fields) do
    pairs =
      Enum.map(fields, fn field ->
        field_str = Atom.to_string(field)
        left = {:attribute_access, [attribute: field_str], [{:variable, [scope: :local], "a"}]}
        right = {:attribute_access, [attribute: field_str], [{:variable, [scope: :local], "b"}]}
        combined = {:binary_op, [operator: :<>, category: :string], [left, right]}
        {:pair, [], [{:literal, [subtype: :symbol], field}, combined]}
      end)

    body = {:function_call, [name: type_name, record: true], pairs}

    [
      {:function_def,
       [
         name: "combine",
         params: [
           {:param, [type: {:variable, [], type_name}], "a"},
           {:param, [type: {:variable, [], type_name}], "b"}
         ],
         visibility: :public,
         arity: 2,
         line: 0
       ], [body]}
    ]
  end

  # -- JSON derivation (v0.21.0) ----------------------------------------------
  #
  # Generates:
  #
  #   fn to_json(x: Record) -> String =
  #     "{\"field1\":" <> to_json(x.field1) <> ",\"field2\":" <> to_json(x.field2) <> "}"
  #
  # Field names map 1:1 to JSON keys. Escaping is delegated to the
  # underlying `to_json/1` protocol method the user (or another
  # derivation) must provide for every field's type. `from_json/1`
  # is reserved for a future release.
  defp derive_json(type_name, fields) do
    body =
      if fields == [] do
        {:literal, [subtype: :string], "{}"}
      else
        field_parts =
          fields
          |> Enum.map(fn field ->
            field_access = {:attribute_access, [attribute: Atom.to_string(field)], [{:variable, [scope: :local], "x"}]}
            nested = {:function_call, [name: "to_json"], [field_access]}

            concat(
              {:literal, [subtype: :string], "\"#{field}\":"},
              nested
            )
          end)
          |> Enum.intersperse({:literal, [subtype: :string], ","})
          |> Enum.reduce(&concat(&2, &1))

        concat(
          concat({:literal, [subtype: :string], "{"}, field_parts),
          {:literal, [subtype: :string], "}"}
        )
      end

    [
      {:function_def,
       [
         name: "to_json",
         params: [{:param, [type: {:variable, [], type_name}], "x"}],
         visibility: :public,
         arity: 1,
         line: 0
       ], [body]}
    ]
  end
end
