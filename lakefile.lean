import Lake
open Lake DSL

package "ITree" where
  version := v!"0.1.0"

lean_lib ITree where
  require qpf from git "https://github.com/alexkeizer/QpfTypes.git" @ "9cfc50cfa0dc561f5b7a1bf08e693b2a52172383"

lean_exe Examples where
  root := `Examples
