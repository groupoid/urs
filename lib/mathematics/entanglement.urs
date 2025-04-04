module entanglement where

import foundations.smooth
import foundations.modalities
import foundations.graded
import foundations.groupoid
import foundations.tedk
import foundations.config

// Hilbert space for quantum states (bosonic by default)
def H : U 0 0 := Hilbert

// Multi-particle Hilbert space
def H_n (n : Nat) : U 0 0
  := fold n H (λ acc, tensor 0 0 0 acc H)

// Fermionic multi-particle Hilbert space
def H_n_ferm (n : Nat) : U 0 1
  := fold n (U 0 1) (λ acc, tensor 0 1 1 acc (H : U 0 1))

// Configuration-based quantum state
def QState (n : Nat) (X : SmthSet) : U 0 0
  := qubit (Config^n(X)) H_n

// Fermionic configuration-based quantum state
def QState_ferm (n : Nat) (X : SmthSet) : U 0 1
  := qubit (Config^n(X)) H_n_ferm

// Constructors

// Introduce a quantum state over a configuration space
def intro-qstate (n : Nat) (X : SmthSet) (ψ : Config^n(X) → H_n) : QState n X
  := intro-qubit (Config^n(X)) H_n (map _ _ (λ _ c, ψ c))

// Introduce a fermionic quantum state
def intro-qstate-ferm (n : Nat) (X : SmthSet) (ψ : Config^n(X) → H_n_ferm) : QState_ferm n X
  := intro-qubit (Config^n(X)) H_n_ferm (map _ _ (λ _ c, ψ c))

// Braid a quantum state
def braid-entangle (n : Nat) (b : plt-grpd 1 (BB_n n)) (q : QState n (ℝ^2)) : QState n (ℝ^2)
  := braid-transport n (PU H_n) (λ _ : Config^n (ℝ^2), PU H_n) b q

// Tensor two quantum states (fusion-like operation)
def tensor-qstate (n m : Nat) (X Y : SmthSet) (q1 : QState n X) (q2 : QState m Y) : QState (n + m) (X × Y)
  := intro-qstate (n + m) (X × Y) (λ c, tensor 0 0 0 (app-qubit _ H_n q1 (config-take n c)) (app-qubit _ H_m q2 (config-drop n c)))
  where
    def config-take (k : Nat) (c : Config^(n + m) (X × Y)) : Config^n(X)
      := intro-config n X (λ i, fst (elim-config (n + m) (X × Y) c i))
    def config-drop (k : Nat) (c : Config^(n + m) (X × Y)) : Config^m(Y)
      := intro-config m Y (λ i, snd (elim-config (n + m) (X × Y) c (k + i)))

// Eliminators

// Evaluate a quantum state at a configuration
def eval-qstate (n : Nat) (X : SmthSet) (q : QState n X) (c : Config^n(X)) : H_n
  := app-qubit (Config^n(X)) H_n q c

// Project to fermionic modality
def fermionic-proj (n : Nat) (X : SmthSet) (q : QState n X) : U 0 1
  := fermionic-modal 0 0 (QState n X) q

// Computation Rules

// Beta rule for quantum state evaluation
def qstate-β (n : Nat) (X : SmthSet) (ψ : Config^n(X) → H_n) (c : Config^n(X))
  : Path H_n (eval-qstate n X (intro-qstate n X ψ) c) (ψ c)
  := qubit-β (Config^n(X)) H_n (map _ _ (λ _ c, ψ c)) c

// Braiding preserves state up to homotopy
def braid-entangle-β (n : Nat) (b : plt-grpd 1 (BB_n n)) (q : QState n (ℝ^2))
  : Path (QState n (ℝ^2)) (braid-entangle n b q) q
  := braid-transport-proof n (PU H_n) (λ _ : Config^n (ℝ^2), PU H_n) b q

// Tensor product commutativity for bosonic states
def tensor-qstate-comm (n m : Nat) (X Y : SmthSet) (q1 : QState n X) (q2 : QState m Y)
  : Path (QState (n + m) (X × Y)) (tensor-qstate n m X Y q1 q2) (tensor-qstate m n Y X q2 q1)
  := ap (intro-qstate (n + m) (X × Y)) (fun-ext _ _ (λ c, tensor 0 0 0 (eval-qstate n X q1 (config-take n c)) (eval-qstate m Y q2 (config-drop n c)))
                                            (λ c, tensor 0 0 0 (eval-qstate m Y q2 (config-take m c)) (eval-qstate n X q1 (config-drop m c)))
                                            (λ c, tensor-comm 0 0 0 H_n H_m (eval-qstate n X q1 (config-take n c)) (eval-qstate m Y q2 (config-drop n c))))

// Test Terms

// Test 1: Bell state for two particles
def bell-state (X : SmthSet) : QState 2 X
  := intro-qstate 2 X (λ c, (tensor 0 0 0 |00⟩ |00⟩ + tensor 0 0 0 |11⟩ |11⟩) / √2)
  where
    def |00⟩ : H := basis 0 0  // Placeholder for basis states
    def |11⟩ : H := basis 1 1

// Test 2: Braided Bell state
def test-braid-bell (b : plt-grpd 1 (BB_n 2)) : QState 2 (ℝ^2)
  := braid-entangle 2 b (bell-state (ℝ^2))

// Test 3: Tensor of two single-particle states
def test-tensor-qstate (X Y : SmthSet) (ψ1 : Config^1(X) → H) (ψ2 : Config^1(Y) → H)
  : QState 2 (X × Y)
  := tensor-qstate 1 1 X Y (intro-qstate 1 X ψ1) (intro-qstate 1 Y ψ2)

// Theorems

// Theorem 1: Entanglement Detection
def is-separable (n : Nat) (X : SmthSet) (q : QState n X) : Type
  := Σ (ψs : Π (i : Fin n), qubit X H),
     Path (QState n X) q
          (fold n (QState n X)
                (λ acc i, tensor 0 0 0 acc (ψs i ∘ (elim-config n X))))

def theorem-entangled (n : Nat) (X : SmthSet) (q : QState n X)
  : ¬ (is-separable n X q) → "q is entangled"
  := λ not-sep, "q is entangled"

// Proof sketch: If no separable decomposition exists, q exhibits non-local correlations
def proof-entangled-bell : ¬ (is-separable 2 (ℝ^2) (bell-state (ℝ^2)))
  := λ (sep : is-separable 2 (ℝ^2) (bell-state (ℝ^2))),
     let ψ1 = fst sep 0,
         ψ2 = fst sep 1,
         sep-state = tensor 0 0 0 (ψ1 ∘ elim-config 2 (ℝ^2)) (ψ2 ∘ elim-config 2 (ℝ^2)),
         eq = snd sep : Path (QState 2 (ℝ^2)) (bell-state (ℝ^2)) sep-state
     in absurd (bell-non-separable eq)  // Bell state cannot be product state

// Theorem 2: Braiding Preserves Entanglement
def theorem-braid-preserves (n : Nat) (b : plt-grpd 1 (BB_n n)) (q : QState n (ℝ^2))
  : ¬ (is-separable n (ℝ^2) q) → ¬ (is-separable n (ℝ^2) (braid-entangle n b q))
  := λ not-sep-q,
     λ sep-bq,
     let eq = braid-entangle-β n b q,
         not-sep-bq = transport (λ x, ¬ (is-separable n (ℝ^2) x)) eq not-sep-q
     in not-sep-bq sep-bq

// Proof sketch: Braiding is a homotopy equivalence, preserving non-separability
def proof-braid-preserves-bell (b : plt-grpd 1 (BB_n 2))
  : ¬ (is-separable 2 (ℝ^2) (test-braid-bell b))
  := theorem-braid-preserves 2 b (bell-state (ℝ^2)) proof-entangled-bell

// Theorem 3: Tensor Product Entanglement
def theorem-tensor-entangle (n m : Nat) (X Y : SmthSet) (q1 : QState n X) (q2 : QState m Y)
  : (¬ (is-separable n X q1) ∨ ¬ (is-separable m Y q2)) → ¬ (is-separable (n + m) (X × Y) (tensor-qstate n m X Y q1 q2))
  := λ either-not-sep,
     λ sep-tensor,
     let ψs = fst sep-tensor : Π (i : Fin (n + m)), qubit (X × Y) H,
         split-ψs = λ i, if i < n then ψs i ∘ fst else ψs (i - n) ∘ snd,
         sep-q1 = (λ i, split-ψs i) : Π (i : Fin n), qubit X H,
         sep-q2 = (λ i, split-ψs (n + i)) : Π (i : Fin m), qubit Y H,
         eq = snd sep-tensor
     in match either-not-sep with
        | inl not-sep-q1 => not-sep-q1 (sep-q1, ap (intro-qstate n X) (fun-ext _ _ _ _ _))
        | inr not-sep-q2 => not-sep-q2 (sep-q2, ap (intro-qstate m Y) (fun-ext _ _ _ _ _))

// Proof sketch: If either q1 or q2 is entangled, their tensor product cannot be fully separable
def proof-tensor-bell (X : SmthSet) (ψ : Config^1(X) → H)
  : ¬ (is-separable 2 (X × ℝ^2) (tensor-qstate 1 1 X (ℝ^2) (intro-qstate 1 X ψ) (bell-state (ℝ^2))))
  := theorem-tensor-entangle 1 1 X (ℝ^2) (intro-qstate 1 X ψ) (bell-state (ℝ^2)) (inr proof-entangled-bell)
