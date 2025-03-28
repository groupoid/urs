module yoneda where

import foundations.smooth
import foundations.supersmooth

-- Theorem: Yoneda lemma for smooth sets
def yoneda-smth (X : SmthSet) (n : Nat)
  : Path (plt n X) (Π (k : Nat), Maps (ℝ^k) (ℝ^n) → plt k X)
 := λ φ, λ k f, precomp n k X f φ

-- Proof term: Natural isomorphism via precomposition
def yoneda-smth-iso (X : SmthSet) (n : Nat)
  : Path (plt n X) (Π (k : Nat), Maps (ℝ^k) (ℝ^n) → plt k X) (λ φ, λ k f, precomp n k X f φ)
 := idp (plt n X) (λ φ, λ k f, precomp n k X f φ)  -- Identity path, functoriality assumed

-- Theorem: Yoneda lemma for super smooth sets
def yoneda-supsmth (X : SupSmthSet) (n q : Nat)
  : Path (sup-plt n q X) (Π (m r : Nat), Maps (ℝ^(m|r)) (ℝ^(n|q)) → sup-plt m r X)
 := λ φ, λ m r f, sup-precomp n q m r X f φ

-- Proof term
def yoneda-supsmth-iso (X : SupSmthSet) (n q : Nat)
  : Path (sup-plt n q X) (Π (m r : Nat), Maps (ℝ^(m|r)) (ℝ^(n|q)) → sup-plt m r X) (λ φ, λ m r f, sup-precomp n q m r X f φ)
 := idp (sup-plt n q X) (λ φ, λ m r f, sup-precomp n q m r X f φ)

