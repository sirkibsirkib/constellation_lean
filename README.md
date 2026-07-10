# constellation

To get started, install the lean toolchain.
Follow the instructions at `https://lean-lang.org/install`, where you will be redirected to VsCode specifically (I know) and their Lean extension, whose README will walk you through the whole thing.

When last I checked, instructs you to open VSCode, install the `Lean 4` plugin, and then open a Lean4 project or file to get the prompt to install the (matching) Lean toolchain. 

After that, I reckon you should have these on your path:
- `elan` for managing your Lean toolchain (like Rust `cargo`)
- `lake` for managing Lean projects and dependencies (like Rust `cargo`)
- `lean` for compiling and interpreting Lean source (like `rustc`)

Once your toolchain is sorted, run these (via the VSCode terminal or otherwise):
```
lake exe cache get
lake build
```

