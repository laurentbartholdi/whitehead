module

public import RequestProject.CombPi1

@[expose] public section

/-!
# Reading a word of generators as an edge loop

The one-way comparison of `RequestProject/SubstOneWay.lean` needs, for every block of the
substitution, a homomorphism out of the free group on the generators of that block into the
fundamental group of a complex.  Such a homomorphism is always given by **concrete loops on the
generators**, and the relations it has to satisfy are then **checked on the concatenated edge
loops**.  This file provides exactly that dictionary for `FiniteChains.Comb.Pi1`:

* `FiniteChains.Comb.wordPath` — the edge loop obtained by concatenating the chosen loops of
  the letters of a word (a letter with the negative sign contributing the reversed loop);
* `FiniteChains.Comb.loopHom` — the homomorphism `FreeGroup G →* π₁(X, a)` determined by a
  family of loops;
* `FiniteChains.Comb.loopHom_mk` — its value on a word is the class of the concatenated loop;
* `FiniteChains.Comb.loopHom_eq_one_of_htpy` — a relation of the block holds in `π₁` as soon as
  the concatenated loop of its word is null-homotopic, which is the form in which a filling is
  actually produced.
-/

namespace FiniteChains
namespace Comb

universe u v

variable {X : Complex2.{u}} {a : X.V} {G : Type v}

/-- The edge path contributed by one signed letter: the chosen loop of the letter, reversed if
the letter carries the negative sign. -/
def germLoopPath (g : G → Loop X a) (gb : G × Bool) : List (X.E × Bool) :=
  if gb.2 then (g gb.1).1 else revPath (g gb.1).1

@[simp] theorem germLoopPath_pos (g : G → Loop X a) (x : G) :
    germLoopPath g (x, true) = (g x).1 := rfl

@[simp] theorem germLoopPath_neg (g : G → Loop X a) (x : G) :
    germLoopPath g (x, false) = revPath (g x).1 := rfl

theorem isPath_germLoopPath (g : G → Loop X a) (gb : G × Bool) :
    IsPath X.src X.tgt (germLoopPath g gb) a a := by
  obtain ⟨x, b⟩ := gb
  cases b
  · exact isPath_revPath (g x).2
  · exact (g x).2

/-- **The edge loop spelled by a word**: the concatenation of the chosen loops of its letters. -/
def wordPath (g : G → Loop X a) (l : List (G × Bool)) : List (X.E × Bool) :=
  (l.map (germLoopPath g)).flatten

@[simp] theorem wordPath_nil (g : G → Loop X a) : wordPath g ([] : List (G × Bool)) = [] := rfl

@[simp] theorem wordPath_cons (g : G → Loop X a) (gb : G × Bool) (l : List (G × Bool)) :
    wordPath g (gb :: l) = germLoopPath g gb ++ wordPath g l := rfl

theorem wordPath_append (g : G → Loop X a) (l l' : List (G × Bool)) :
    wordPath g (l ++ l') = wordPath g l ++ wordPath g l' := by
  simp [wordPath]

theorem isPath_wordPath (g : G → Loop X a) (l : List (G × Bool)) :
    IsPath X.src X.tgt (wordPath g l) a a := by
  induction l with
  | nil => exact rfl
  | cons gb l ih =>
      rw [wordPath_cons]
      exact isPath_append_iff.mpr ⟨a, isPath_germLoopPath g gb, ih⟩

/-- The loop of a word, as an element of `Loop X a`. -/
def wordLoopOf (g : G → Loop X a) (l : List (G × Bool)) : Loop X a :=
  ⟨wordPath g l, isPath_wordPath g l⟩

/-- **The homomorphism determined by concrete loops on the generators.** -/
def loopHom (g : G → Loop X a) : FreeGroup G →* Pi1 X a :=
  FreeGroup.lift (fun x => Pi1.mk (g x))

@[simp] theorem loopHom_of (g : G → Loop X a) (x : G) :
    loopHom g (FreeGroup.of x) = Pi1.mk (g x) := by
  simp [loopHom]

theorem pi1_mk_append (p q : Loop X a) :
    Pi1.mk ⟨p.1 ++ q.1, isPath_append_iff.mpr ⟨a, p.2, q.2⟩⟩ = Pi1.mk p * Pi1.mk q := rfl

theorem pi1_mk_revPath (p : Loop X a) :
    Pi1.mk ⟨revPath p.1, isPath_revPath p.2⟩ = (Pi1.mk p)⁻¹ := rfl

/-- **The value of the homomorphism on a word is the class of the concatenated loop.** -/
theorem loopHom_mk (g : G → Loop X a) (l : List (G × Bool)) :
    loopHom g (FreeGroup.mk l) = Pi1.mk (wordLoopOf g l) := by
  induction l with
  | nil =>
      simp only [loopHom, FreeGroup.lift_mk, List.map_nil, List.prod_nil]
      rfl
  | cons gb l ih =>
      obtain ⟨x, b⟩ := gb
      have hsplit : ((x, b) :: l) = [(x, b)] ++ l := rfl
      rw [hsplit, ← FreeGroup.mul_mk, map_mul, ih]
      have hcat : wordLoopOf g ([(x, b)] ++ l)
          = ⟨(wordLoopOf g [(x, b)]).1 ++ (wordLoopOf g l).1,
              isPath_append_iff.mpr ⟨a, (wordLoopOf g [(x, b)]).2, (wordLoopOf g l).2⟩⟩ := by
        apply Subtype.ext
        simp [wordLoopOf, wordPath]
      rw [hcat, pi1_mk_append]
      congr 1
      cases b
      · rw [show FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ from rfl, map_inv, loopHom_of]
        have : wordLoopOf g [(x, false)] = ⟨revPath (g x).1, isPath_revPath (g x).2⟩ := by
          apply Subtype.ext
          simp [wordLoopOf, wordPath]
        rw [this, pi1_mk_revPath]
      · rw [show FreeGroup.mk [(x, true)] = FreeGroup.of x from rfl, loopHom_of]
        congr 1
        apply Subtype.ext
        simp [wordLoopOf, wordPath]

/-- **A relation is checked on the concatenated loop**: if the loop spelled by the word `l` is
null-homotopic, the word dies in `π₁`. -/
theorem loopHom_eq_one_of_htpy (g : G → Loop X a) {l : List (G × Bool)}
    (h : Htpy X a a (wordPath g l) []) : loopHom g (FreeGroup.mk l) = 1 := by
  rw [loopHom_mk]
  exact Quotient.sound h

end Comb
end FiniteChains
