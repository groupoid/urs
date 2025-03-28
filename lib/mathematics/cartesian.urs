module cartesian where

import foundations.smooth

-- Theorem: Cartesian closure of smooth sets
def cart-closed (U X F : SmthSet) (n : Nat)
  : Path (plt n (Maps X F)) (plt n (λ k, Π (x : plt k X), plt k F))
 := λ φ, λ k x, app-map X F φ k x

-- Proof term: Adjointness via currying/uncurrying
def cart-closed-iso (U X F : SmthSet) (n : Nat)
  : Path (plt n (Maps X F)) (plt n (λ k, Π (x : plt k (U × X)), plt k F))
 := λ φ, λ k ux, app-map X F φ k (snd ux)  -- assumes U × X pairing

-- Computation check
def cart-closed-β (U X F : SmthSet) (n : Nat) (φ : plt n (Maps X F)) (x : plt n X)
  : Path (plt n F) (app-map X F φ n x) (app-map X F φ n x)
 := map-β X F (λ k x, app-map X F φ k x) n x
