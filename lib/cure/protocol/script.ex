defmodule Cure.Protocol.Script do
  @moduledoc """
  Session-typed binary protocol representation for the `protocol`
  container (v0.27.0).

  A *script* describes an ordered sequence of steps between a finite
  set of named roles. Each step is a tagged tuple:

    * `{:msg, from_role, to_role, tag, args}` -- one role sends a
      message to another. `tag` is the message tag string; `args` is
      a list of type-expression strings.
    * `{:loop, body}` -- the enclosed body repeats forever. The
      verifier represents this as a self-loop in the projected FSM.
    * `{:choose, [branch1, branch2, ...]}` -- an active role picks one
      of the branches. Each branch is a list of steps; the first step
      of every branch must share the same sender (that's the active
      role).
    * `{:offer, [branch1, branch2, ...]}` -- a passive role accepts
      one of the branches. First-step receiver must match across
      branches.
    * `{:end}` -- terminates the protocol.

  A script is always a pair `{name, roles, body}` wrapped in a
  struct.
  """

  @enforce_keys [:name, :roles, :body]
  defstruct [:name, :roles, :body]

  @type role :: String.t()
  @type tag :: String.t()
  @type type_expr :: String.t()

  @type step ::
          {:msg, role(), role(), tag(), [type_expr()]}
          | {:loop, [step()]}
          | {:choose, [[step()]]}
          | {:offer, [[step()]]}
          | {:end_, []}

  @type t :: %__MODULE__{
          name: String.t(),
          roles: [role()],
          body: [step()]
        }

  @doc """
  Project the script onto a single role, producing an FSM-style
  transition list usable by `Cure.Temporal.Checker.from_fsm/2`. States
  are labelled `S<index>`; transitions carry the originating message
  tag as the event (prefixed with `send`, `recv`, or `idle` depending
  on the projected role's involvement in the step).
  """
  @spec project(t(), role()) :: [map()]
  def project(%__MODULE__{body: body} = script, role) do
    ensure_role!(script, role)
    {trans, _next} = do_project(body, role, "S0", 1, [])
    Enum.reverse(trans)
  end

  defp do_project([], _role, _state, idx, acc), do: {acc, idx}

  defp do_project([{:msg, from, to, tag, _args} | rest], role, state, idx, acc) do
    next_state = "S#{idx}"
    event_tag = message_event(from, to, tag, role)

    new_trans =
      cond do
        from == role ->
          [%{from: state, event: "send #{event_tag}", to: next_state, event_kind: :normal} | acc]

        to == role ->
          [%{from: state, event: "recv #{event_tag}", to: next_state, event_kind: :normal} | acc]

        true ->
          # Third-party message; the projected role is idle but still
          # advances to keep step alignment across all projections.
          [%{from: state, event: "idle #{event_tag}", to: next_state, event_kind: :normal} | acc]
      end

    do_project(rest, role, next_state, idx + 1, new_trans)
  end

  defp do_project([{:loop, body} | rest], role, state, idx, acc) do
    # Project the body onto the current role; the final state loops
    # back to the starting state.
    {sub_trans, next_idx} = do_project(body, role, state, idx, [])

    loop_edge =
      case sub_trans do
        [] ->
          []

        [head | _] ->
          first = List.last(sub_trans)
          [%{from: head.to, event: "loop_back", to: first.from, event_kind: :normal}]
      end

    do_project(rest, role, state, next_idx, loop_edge ++ sub_trans ++ acc)
  end

  defp do_project([{:choose, branches} | rest], role, state, idx, acc) do
    {branch_trans, next_idx, join_states} =
      Enum.reduce(branches, {[], idx, []}, fn branch, {trans, i, joins} ->
        {bt, ni} = do_project(branch, role, state, i, [])

        join_state =
          case bt do
            [head | _] -> head.to
            [] -> state
          end

        {bt ++ trans, ni, [join_state | joins]}
      end)

    # After the branch, all converge to a synthetic join state.
    join = "S#{next_idx}"

    join_edges =
      Enum.map(join_states, fn s ->
        %{from: s, event: "join", to: join, event_kind: :normal}
      end)

    do_project(rest, role, join, next_idx + 1, join_edges ++ branch_trans ++ acc)
  end

  defp do_project([{:offer, branches} | rest], role, state, idx, acc) do
    # Structurally the same projection as :choose; the semantic
    # difference (active vs passive) is enforced by the verifier.
    do_project([{:choose, branches} | rest], role, state, idx, acc)
  end

  defp do_project([{:end_, []} | _rest], _role, state, idx, acc) do
    {[%{from: state, event: "end", to: "END", event_kind: :normal} | acc], idx + 1}
  end

  defp message_event(from, to, tag, _role), do: "#{from}->#{to}:#{tag}"

  defp ensure_role!(%__MODULE__{roles: roles}, role) do
    if role not in roles do
      raise ArgumentError, "unknown role #{inspect(role)}; known: #{inspect(roles)}"
    end
  end
end
