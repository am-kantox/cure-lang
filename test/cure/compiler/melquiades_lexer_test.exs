defmodule Cure.Compiler.MelquiadesLexerTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Lexer
  alias Cure.Compiler.Token

  defp lex!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    tokens
  end

  defp non_eof(tokens), do: Enum.reject(tokens, &(&1.type == :eof))

  describe "Melquiades operator tokens" do
    test "ASCII form `<-|` produces a single :melquiades token" do
      tokens = lex!("pid <-| msg")

      assert [
               %Token{type: :identifier, value: "pid"},
               %Token{type: :melquiades, value: "<-|"},
               %Token{type: :identifier, value: "msg"}
             ] = non_eof(tokens)
    end

    test "unicode envelope `\u2709` produces a single :melquiades token with the unicode lexeme" do
      tokens = lex!("pid \u2709 msg")

      assert [
               %Token{type: :identifier, value: "pid"},
               %Token{type: :melquiades, value: "\u2709"},
               %Token{type: :identifier, value: "msg"}
             ] = non_eof(tokens)
    end

    test "Melquiades operator does not require surrounding spaces" do
      tokens = lex!("pid<-|msg")

      assert [
               %Token{type: :identifier, value: "pid"},
               %Token{type: :melquiades, value: "<-|"},
               %Token{type: :identifier, value: "msg"}
             ] = non_eof(tokens)
    end

    test "lone `<` still tokenises as :lt" do
      assert [%Token{type: :lt}, %Token{type: :integer, value: 3}] = non_eof(lex!("< 3"))
    end

    test "`<=` still tokenises as :lte" do
      assert [%Token{type: :lte}, %Token{type: :integer, value: 3}] = non_eof(lex!("<= 3"))
    end

    test "`<<` still tokenises as :binary_open" do
      assert [%Token{type: :binary_open}, %Token{type: :integer, value: 1}, %Token{type: :binary_close}] =
               non_eof(lex!("<<1>>"))
    end

    test "`<>` still tokenises as :string_concat" do
      assert [%Token{type: :string, value: "a"}, %Token{type: :string_concat}, %Token{type: :string, value: "b"}] =
               non_eof(lex!(~s("a" <> "b")))
    end

    test "`<-` is not a Melquiades operator (it is `<` + `-` for comprehensions/binary generators)" do
      # The generator arrow `<-` is emitted as `:lt` + `:minus`; we must
      # NOT fold it into a new token. A standalone `<-` here just produces
      # those two tokens and the subsequent identifier.
      tokens = non_eof(lex!("x <- ys"))

      assert [
               %Token{type: :identifier, value: "x"},
               %Token{type: :lt},
               %Token{type: :minus},
               %Token{type: :identifier, value: "ys"}
             ] = tokens
    end

    test "stray 0xE2 byte that is not `\u2709` is rejected as :unexpected_character" do
      # `\u00E2` is LATIN SMALL LETTER A WITH CIRCUMFLEX -- two bytes in
      # UTF-8 (0xC3 0xA2), not starting with 0xE2, so it does not trigger
      # the envelope path.
      # `\u2714` (CHECK MARK) starts with 0xE2 0x9C 0x94, sharing the
      # first two bytes of the envelope but diverging on the third. The
      # lexer must reject it, not silently accept it as the Melquiades
      # operator.
      assert {:error, {:unexpected_character, 0xE2, 1, 1}} =
               Lexer.tokenize("\u2714", emit_events: false)
    end
  end
end
