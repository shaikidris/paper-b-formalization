# Paper B EX2.2 unattended runner

The runner resumes the existing Gemini 4 Carbon Medium conversation and checks three declarations, in order.

| Declaration | What it establishes |
|---|---|
| `takeWhile_predecessor_losses_iff` | The selected prefix contains exactly the ancestors that lose every predecessor. |
| `sweep_parent_eq_for_reused_pair_key` | A repeated canonical pair selects the same parent from the fixed earlier labels. |
| `sweep_step_preserves_proper_loss_labels` | A single topological step preserves the nested chain invariant and detects exactly the canonical cuts that properly lose the new vertex. |

The full finite sweep, its forest representation, and paper-level certification remain tracked under EX2.2. The separate costed construction is EX2.4. [EX2.2 and related tasks](../TASKS.md#ex22)

## Monitoring

Open the [live status](../../.collaboration/unattended-ex22/STATUS.md) to see the batch while it runs. It shows the current declaration and the state of each item. Each accepted declaration gets a scoped Lean build, an axiom report and a local commit. The checkpoint's build log, provider receipt and paper-statement contract are linked through the verification record in the tracker.

The locally loaded LaunchAgent runs the batch once in the logged-in user's session. Each Carbon turn has a seven-minute deadline and the batch allows one repair turn for a failed declaration. A sealed checkpoint can proceed even when the chat stream lingers. The runner stops after success or a concrete blocker and requests one macOS desktop notification. The status file records whether macOS accepted that request.

Only the existing authenticated Antigravity profile gets the task contract and, if needed, scoped Lean diagnostics. The runner checks candidate declarations in a restricted scratch Lean process before applying them. Repository changes are limited to checked proofs, their evidence and the tracker. If the checkout changes or a Git hook fails, inspect the local evidence before starting another batch.

From the project root, run an offline preflight of the signatures, sandbox and toolchain. The command also checks the existing Carbon session state.

```sh
/usr/local/bin/python3 -B paper-b-formalization/unattended/run_ex22.py --check
```
