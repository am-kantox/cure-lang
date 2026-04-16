import { ExtensionContext, workspace } from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export function activate(context: ExtensionContext): void {
  const config = workspace.getConfiguration("cure");
  const command: string = config.get("lsp.path", "cure");
  const args: string[] = config.get("lsp.args", ["lsp"]);

  const serverOptions: ServerOptions = {
    run: { command, args, transport: TransportKind.stdio },
    debug: { command, args, transport: TransportKind.stdio },
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "cure" }],
    synchronize: {
      fileEvents: workspace.createFileSystemWatcher("**/*.cure"),
    },
  };

  client = new LanguageClient(
    "cure",
    "Cure Language Server",
    serverOptions,
    clientOptions
  );

  context.subscriptions.push(client.start());
}

export function deactivate(): Thenable<void> | undefined {
  return client?.stop();
}
