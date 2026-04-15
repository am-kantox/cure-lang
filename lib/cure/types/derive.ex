defmodule Cure.Types.Derive do
  @moduledoc """
  Automatic typeclass instance derivation for records and ADTs.

  Generates protocol method implementations from a type's structure:

  - **Show**: concatenates field names and `show()` of each field value
  - **Eq**: structural equality (all fields equal)
  - **Ord**: lexicographic comparison of fields

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

  def derive(_typeclass, _type_name, _fields), do: []

  @doc """
  Check if a typeclass can be derived for a type.
  """
  @spec can_derive?(atom()) :: boolean()
  def can_derive?(:show), do: true
  def can_derive?(:eq), do: true
  def can_derive?(:ord), do: true
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
end
