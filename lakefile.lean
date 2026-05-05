import Lake

open System Lake DSL

package StringSearchLean where version := v!"0.1.0"

lean_lib StringSearchLean
require Velvet from git "https://github.com/verse-lab/velvet.git" @ "master"

@[default_target] lean_exe stringsearchlean where root := `Main
