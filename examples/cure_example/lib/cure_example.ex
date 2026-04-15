defmodule CureExample do
  @moduledoc """
  Demonstrates calling Cure-compiled BEAM modules from Elixir.

  Cure compiles `.cure` source files into Elixir-style BEAM modules with
  a `Cure.` prefix (e.g., `mod Calculator` becomes `Cure.Calculator`).
  These modules are callable from Elixir like any other module.
  """

  @doc """
  Greets a person using the Cure `Greeter` module.

      iex> CureExample.greet("World")
      "Hello, World!"
  """
  def greet(name), do: :"Cure.Greeter".hello(name)

  @doc """
  Says farewell using the Cure `Greeter` module.

      iex> CureExample.farewell("World")
      "Goodbye, World. See you soon!"
  """
  def farewell(name), do: :"Cure.Greeter".farewell(name)

  @doc """
  Computes n! using the Cure `Calculator` module.

      iex> CureExample.factorial(10)
      3628800
  """
  def factorial(n), do: :"Cure.Calculator".factorial(n)

  @doc """
  Computes the n-th Fibonacci number using the Cure `Calculator` module.

      iex> CureExample.fibonacci(10)
      55
  """
  def fibonacci(n), do: :"Cure.Calculator".fibonacci(n)

  @doc """
  Classifies an integer as "positive", "negative", or "zero".

      iex> CureExample.classify(42)
      "positive"
      iex> CureExample.classify(-1)
      "negative"
      iex> CureExample.classify(0)
      "zero"
  """
  def classify(n), do: :"Cure.Calculator".classify(n)

  @doc """
  Safe division that returns `{:ok, result}` or `{:error, reason}`.

      iex> CureExample.safe_divide(10, 2)
      {:ok, 5}
      iex> CureExample.safe_divide(10, 0)
      {:error, "division by zero"}
  """
  def safe_divide(a, b), do: :"Cure.Calculator".safe_divide(a, b)

  @doc """
  Runs a demo showing all the Cure modules in action.
  """
  def demo do
    IO.puts("--- Cure Example: Greeter ---")
    IO.puts(:"Cure.Greeter".hello("Elixir"))
    IO.puts(:"Cure.Greeter".farewell("Elixir"))

    IO.puts("\n--- Cure Example: Calculator ---")
    IO.puts("5 + 3 = #{:"Cure.Calculator".add(5, 3)}")
    IO.puts("10 - 4 = #{:"Cure.Calculator".sub(10, 4)}")
    IO.puts("6 * 7 = #{:"Cure.Calculator".mul(6, 7)}")
    IO.puts("10! = #{:"Cure.Calculator".factorial(10)}")
    IO.puts("fib(10) = #{:"Cure.Calculator".fibonacci(10)}")

    IO.puts("\n--- Cure Example: Pattern Guards ---")
    IO.puts("classify(42) = #{:"Cure.Calculator".classify(42)}")
    IO.puts("classify(-1) = #{:"Cure.Calculator".classify(-1)}")
    IO.puts("classify(0)  = #{:"Cure.Calculator".classify(0)}")

    IO.puts("\n--- Cure Example: Result Types ---")
    IO.puts("safe_divide(10, 2) = #{inspect(:"Cure.Calculator".safe_divide(10, 2))}")
    IO.puts("safe_divide(10, 0) = #{inspect(:"Cure.Calculator".safe_divide(10, 0))}")
  end
end
