defmodule CureSite.Pages.Page do
  @enforce_keys [:id, :title, :body, :description, :order]
  defstruct [:id, :title, :body, :description, :order]

  def build(filename, attrs, body) do
    id = filename |> Path.rootname() |> Path.split() |> List.last()
    struct!(__MODULE__, [id: id, body: body] ++ Map.to_list(attrs))
  end
end
