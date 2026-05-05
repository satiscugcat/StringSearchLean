import Velvet.Std
import CaseStudies.TestingUtil 

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method kmp_table (W: Array Nat) return (T: Array (Option Nat))
  do
    let mut result := Array.replicate W.size Option.none
    let mut pos := 1
    let mut cnd := 0
    while pos < W.size do
      if W[pos]! = W[cnd]! then
        result := result.set! pos (result[cnd]!)
      else
        result := result.set! pos (Option.some cnd)
        let mut cnd' := Option.some cnd
        while cnd' ≠ Option.none && W[pos]! ≠ W[cnd]! do
          match cnd' with
          | none => cnd' := cnd'
          | some val =>
            cnd' := result[val]!
            match cnd' with
            | none => cnd' := cnd'
            | some val' => cnd := val'
        pos := pos + 1
        match cnd' with
        | none => cnd := 0
        | some val => cnd := val + 1
    return result


method kmp_search (S: Array Nat) (W: Array Nat)  return (position: Option Nat)
  do
    let mut j := 0
    let mut k := 0
    let T ← kmp_table W
    let mut result := Option.none
    while j < S.size do
      if W[k]! = S[j]! then
        j := j + 1
        k := k + 1
        if k = W.size then result := Option.some (j - k) 
      else
        match T[k]! with
        | none => 
          k := 0
          j := j + 1
        | some val =>
          k := val
    return result

-- #print kmp_search -- verifying that if-then-else parsing is done appropriately
-- #print kmp_table 
