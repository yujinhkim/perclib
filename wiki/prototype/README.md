# Compatibility entry point

The single-page prototype is retired. Handwritten site source is in `../src/`,
article sources are in `../articles/`, and generated output is in `../dist/`.

Existing CI still runs `npm ci && npm run build` here. This installs the same
pinned KaTeX version and delegates to the parent build. New users should run
`npm ci && npm run build` in `wiki/`. Neither route invokes Lean.

Keep this bridge until the CI owner changes the workflow's working directory and
lockfile path to `wiki/`; then remove this directory in a separate change.
