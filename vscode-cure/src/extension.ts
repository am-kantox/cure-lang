import {
  commands,
  ExtensionContext,
  OutputChannel,
  window,
  workspace,
} from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

/**
 * Single active LanguageClient instance. Recreated when the user
 * invokes `Cure: Restart Language Server` or when the LSP-related
 * settings change.
 */
let client: LanguageClient | undefined;
let outputChannel: OutputChannel | undefined;

export async function activate(context: ExtensionContext): Promise<void> {
  outputChannel = window.createOutputChannel("Cure Language Server");
  context.subscriptions.push(outputChannel);

  await startClient(context);

  // Recreate the client when settings under `cure.*` change. The
  // LSP is launched with explicit `command` / `args` / `env`, so we
  // must restart to pick them up.
  context.subscriptions.push(
    workspace.onDidChangeConfiguration(async (e) => {
      if (
        e.affectsConfiguration("cure.lsp") ||
        e.affectsConfiguration("cure.trace.server")
      ) {
        await restartClient(context);
      }
    })
  );

  // Expose a manual restart command for users who want to force a
  // fresh connection after rebuilding the `cure` escript.
  context.subscriptions.push(
    commands.registerCommand("cure.restartLsp", async () => {
      await restartClient(context);
      window.showInformationMessage("Cure: Language server restarted.");
    })
  );
}

export async function deactivate(): Promise<void> {
  if (!client) {
    return;
  }
  await client.stop();
  client = undefined;
}

async function startClient(context: ExtensionContext): Promise<void> {
  const config = workspace.getConfiguration("cure");
  const command: string = config.get("lsp.path", "cure");
  const args: string[] = config.get("lsp.args", ["lsp"]);
  const env: Record<string, string> = config.get("lsp.env", {});

  const runOptions = {
    command,
    args,
    transport: TransportKind.stdio,
    options: {
      env: { ...process.env, ...env },
    },
  };

  const serverOptions: ServerOptions = {
    run: runOptions,
    debug: runOptions,
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "cure" }],
    synchronize: {
      fileEvents: workspace.createFileSystemWatcher("**/*.cure"),
    },
    outputChannel,
  };

  client = new LanguageClient(
    "cure",
    "Cure Language Server",
    serverOptions,
    clientOptions
  );

  // `client.start()` returns Promise<void> in vscode-languageclient
  // 9.x; the LanguageClient itself implements Disposable, so push
  // it onto `context.subscriptions` to guarantee shutdown on
  // extension deactivate.
  context.subscriptions.push(client);

  try {
    await client.start();
  } catch (err) {
    const message = err instanceof Error ? err.message : String(err);
    window.showErrorMessage(
      `Cure: failed to start language server (${command} ${args.join(" ")}): ${message}`
    );
  }
}

async function restartClient(context: ExtensionContext): Promise<void> {
  if (client) {
    try {
      await client.stop();
    } catch {
      // Swallow errors from stop() -- a dead server is still dead.
    }
    client = undefined;
  }
  await startClient(context);
}
