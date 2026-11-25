import Std

/-!
This file checks the bracketing argument for prefixes before the final atomic
marker. The rule evaluator includes arbitrary directional suffixes and optional
substitution. The SAT and Clique reductions and the final application are
proved in hardness.md.
-/

namespace PureCCG

inductive Atom where
  | control | marker | cell
  deriving DecidableEq

structure Name where
  sort : Atom
  index : Nat
  deriving DecidableEq

inductive Dir where
  | fwd | bwd
  deriving DecidableEq

inductive Cat where
  | atom (a : Name)
  | slash (left : Cat) (dir : Dir) (right : Cat)
  deriving DecidableEq

abbrev Arg := Dir × Cat

/-- A category written as its atomic target and left spine, innermost argument first. -/
structure Spine where
  head : Name
  args : List Arg
  deriving DecidableEq

def flatten : Cat → Spine
  | .atom a => ⟨a, []⟩
  | .slash x d y => let s := flatten x; ⟨s.head, s.args ++ [(d,y)]⟩

/-- Strip precisely the concrete prefix from the secondary category's argument list. -/
def strip : List Arg → List Arg → Option (List Arg)
  | [], rest => some rest
  | _ :: _, [] => none
  | p :: ps, q :: qs => if p = q then strip ps qs else none

/-- One oriented rule, with either zero or one shared arguments. The excess may have
any length and arbitrary slash directions. A finite degree cap only removes steps. -/
def step (d : Dir) (substitution : Bool) (primary secondary : Spine) : Option Spine := do
  let (shared, rest) ← if substitution then
    match primary.args.reverse with
    | a :: t => some ([a], t)
    | [] => none
  else some ([], primary.args.reverse)
  let (dir,y) :: xs := rest | none
  if dir != d then none else
    let bridge := flatten y
    if secondary.head != bridge.head then none else
      let β ← strip (bridge.args ++ shared) secondary.args
      return ⟨primary.head, xs.reverse ++ shared ++ β⟩

def headName (a : Atom) (i : Nat) : Name := ⟨a,i⟩
def atom (a : Atom) (i : Nat) := Cat.atom (headName a i)
def tag (i : Nat) : Arg := (.fwd, atom .marker i)
def val (i : Nat) : Arg := (.fwd, atom .cell i)

def packet (a : Name) (v : List Nat) (t : Nat) : Spine :=
  ⟨a, v.map val ++ [tag t]⟩

def readOp (h h' b : Nat) : Spine :=
  ⟨headName .control h', [(.bwd, .slash (atom .control h) .fwd (atom .cell b))]⟩

def writeOp (s : Nat) (v : List Nat) (t : Nat) : Spine := packet (headName .marker s) v t

theorem forward_write (h : Name) (q v : List Nat) (t s t' : Nat) :
    step .fwd false (packet h q t) (packet (headName .marker s) v t') =
      (if s = t then some (packet h (q ++ v) t') else none) := by
  simp [step, packet, flatten, tag, atom, headName, strip, List.append_assoc]

theorem backward_read (h h' k : Nat) (q : List Nat) (t b : Nat) :
    step .bwd false (readOp h h' b) (packet (headName .control k) q t) =
      (match q with
       | [] => none
       | x :: xs => if k = h ∧ x = b then some (packet (headName .control h') xs t) else none) := by
  cases q <;> simp [step, packet, readOp, flatten, tag, val, atom, headName, strip]
  all_goals grind

theorem packet_as_backward (h : Name) (q : List Nat) (t : Nat) (r : Spine) (sub : Bool) :
    step .bwd sub (packet h q t) r = none := by
  cases sub <;> simp [step, packet, tag, atom, headName]
  rw [← List.map_reverse]
  cases q.reverse <;> rfl


/-- Forward substitution would require a secondary whose target is a cell. -/
theorem no_substitution (h : Name) (q : List Nat) (t : Nat) (r : Spine)
    (hr : r.head.sort ≠ .cell) : step .fwd true (packet h q t) r = none := by
  simp [step, packet, tag, ← List.map_reverse]
  cases q.reverse with
  | nil => rfl
  | cons x xs =>
    have hx : r.head ≠ headName .cell x := fun e => hr (congrArg Name.sort e)
    simp [val, flatten, atom, hx]

theorem read_as_forward (h k b : Nat) (r : Spine) (sub : Bool) :
    step .fwd sub (readOp h k b) r = none := by
  cases sub <;> rfl

theorem read_substitute (h k b : Nat) (r : Spine) :
    step .bwd true (readOp h k b) r = none := rfl

theorem forward_packet_read (p : Name) (q : List Nat) (t h k b : Nat) :
    step .fwd false (packet p q t) (readOp h k b) = none := by
  simp [step, packet, readOp, tag, atom, flatten, headName]

theorem backward_read_write (h k b s t : Nat) (v : List Nat) :
    step .bwd false (readOp h k b) (packet (headName .marker s) v t) = none := by
  simp [step, readOp, packet, flatten, atom, headName]

theorem backward_read_read (h k b h' k' b' : Nat) :
    step .bwd false (readOp h k b) (readOp h' k' b') = none := by
  simp [step, readOp, flatten, atom, headName, strip]

/-- Surface order is left to right, with the primary on the right for backward rules. -/
def Combines (l r o : Spine) : Prop :=
  ∃ sub : Bool, step .fwd sub l r = some o ∨ step .bwd sub r l = some o

inductive Shape where
  | core (h : Nat) (q : List Nat) (t : Nat)
  | write (s : Nat) (v : List Nat) (t : Nat)
  | read (h h' b : Nat)

def Shape.repr : Shape → Spine
  | .core h q t => packet (headName .control h) q t
  | .write s v t => writeOp s v t
  | .read h h' b => readOp h h' b

/-- A right subtree containing the leftmost seed is excluded by surface order. -/
inductive Op where
  | write (s : Nat) (v : List Nat) (t : Nat)
  | read (h h' b : Nat)

def Op.shape : Op → Shape
  | .write s v t => .write s v t
  | .read h h' b => .read h h' b

/-- The queue protocol in surface word order. This definition has no CCG rules. -/
def applyOp : Shape → Op → Option Shape
  | .core h q s, .write a v t =>
    if a = s then some (.core h (q ++ v) t) else none
  | .write i u s, .write a v t =>
    if a = s then some (.write i (u ++ v) t) else none
  | .core k (x :: xs) t, .read h h' b =>
    if k = h ∧ x = b then some (.core h' xs t) else none
  | _, _ => none

theorem head_safe (r : Shape) : r.repr.head.sort ≠ .cell := by cases r <;> simp [Shape.repr, packet, writeOp, readOp, headName]

/-- Complete inversion of one genuine rule instance when the right input is an
operation. Composition may copy an arbitrary suffix in either direction. -/
theorem local_sound {o : Spine} (l : Shape) (r : Op)
    (rule : Combines l.repr r.shape.repr o) :
    (applyOp l r).map Shape.repr = some o := by
  obtain ⟨sub, rule⟩ := rule
  have hL := head_safe l
  have hR := head_safe r.shape
  cases l <;> cases r <;> cases sub <;>
    simp only [Shape.repr, Op.shape, writeOp] at * <;>
    simp_all only [forward_write, backward_read, packet_as_backward,
      read_as_forward, read_substitute, forward_packet_read, backward_read_write,
      backward_read_read, reduceCtorEq, false_or, or_false]
  all_goals first
    | rw [no_substitution _ _ _ _ hR] at rule; contradiction
    | contradiction
    | split at rule <;> simp_all [applyOp, Shape.repr, writeOp]
    | rename_i q t h h' b; cases q <;> simp_all [applyOp, Shape.repr]


/-- Extend a spine by any suffix, retaining all slash directions and categories. -/
def extend (x : Spine) (u : List Arg) : Spine := ⟨x.head, x.args ++ u⟩

theorem strip_append (a b : List Arg) : strip a (a ++ b) = some b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simpa [strip] using ih

/-- Every forward or backward composition instance is covered by the evaluator. -/
theorem composition_scheme (x : Spine) (y : Cat) (β : List Arg) (d : Dir) :
    step d false (extend x [(d,y)]) (extend (flatten y) β) = some (extend x β) := by
  simp [step, extend, strip_append]

/-- Every forward or backward substitution instance with one shared argument is covered. -/
theorem substitution_scheme (x : Spine) (y : Cat) (a : Arg) (β : List Arg) (d : Dir) :
    step d true (extend x [(d,y),a]) (extend (flatten y) (a :: β)) =
      some (extend x (a :: β)) := by
  have hs := strip_append ((flatten y).args ++ [a]) β
  simp only [List.append_assoc, List.singleton_append] at hs
  simp [step, extend, hs, List.append_assoc]

def run (s : Shape) : List Op → Option Shape
  | [] => some s
  | a :: rest => (applyOp s a).bind (fun t => run t rest)

theorem run_append (l r : List Op) (s : Shape) :
    run s (l ++ r) = (run s l).bind (fun t => run t r) := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp [run, ih, Option.bind_assoc]

theorem write_assoc (s : Shape) (i j k : Nat) (v u : List Nat) :
    ((applyOp s (.write i v j)).bind (fun s' => applyOp s' (.write j u k))) =
      applyOp s (.write i (v ++ u) k) := by
  cases s <;> simp [applyOp]
  all_goals split <;> simp_all [List.append_assoc]

/-- Every bracketing of an interval of operation tokens. -/
inductive Tree : List Op → Spine → Prop
  | leaf (a : Op) : Tree [a] a.shape.repr
  | join {u v l r o} : Tree u l → Tree v r → Combines l r o → Tree (u ++ v) o

theorem merge_ops (a b : Op) {o : Spine} (h : Combines a.shape.repr b.shape.repr o) :
    ∃ c : Op, c.shape.repr = o ∧
      ∀ s, ((applyOp s a).bind (fun s' => applyOp s' b)) = applyOp s c := by
  have inv := local_sound a.shape b h
  cases a <;> cases b <;> simp [applyOp, Op.shape] at inv
  obtain ⟨rfl, rfl⟩ := inv
  exact ⟨_, rfl, fun s => write_assoc s _ _ _ _ _⟩

/-- Every successful operation subtree acts exactly like one operation on every
starting packet. Therefore coalescing writes inside a tree cannot reorder them. -/
theorem op_tree_sound {ops o} (tree : Tree ops o) :
    ∃ c : Op, c.shape.repr = o ∧ ∀ s, run s ops = applyOp s c := by
  induction tree with
  | leaf a => exact ⟨a, rfl, fun s => by simp [run]⟩
  | join left right rule ihL ihR =>
    obtain ⟨a, rfl, ha⟩ := ihL
    obtain ⟨b, rfl, hb⟩ := ihR
    obtain ⟨c, hc, hab⟩ := merge_ops a b rule
    exact ⟨c, hc, fun s => by simp only [run_append, ha, hb, hab]⟩

/-- Every binary bracketing with the seed token at the left edge. -/
inductive Prefix (seed : Shape) : List Op → Spine → Prop
  | start : Prefix seed [] seed.repr
  | join {u v l r o} : Prefix seed u l → Tree v r → Combines l r o → Prefix seed (u ++ v) o

theorem prefix_sound {seed ops o} (p : Prefix seed ops o) :
    ∃ s, run seed ops = some s ∧ s.repr = o := by
  induction p with
  | start => exact ⟨_, rfl, rfl⟩
  | join left right rule ih =>
    obtain ⟨s, hs, rfl⟩ := ih
    obtain ⟨r, rfl, hr⟩ := op_tree_sound right
    obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp (local_sound s r rule)
    exact ⟨t, by simp only [run_append, hs, Option.bind_some, hr, ht], he⟩

end PureCCG
