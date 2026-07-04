import Lake
open Lake DSL

package «HypersequentCalculus» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib «HypersequentCalculus» where
  globs := #[.one `HypersequentCalculus, .submodules `Modal]
