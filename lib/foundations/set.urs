module set where

-- Universe hierarchy
def U (i : Nat) : Type := U_i
def U₀ : Type := U 0
def U₁ : Type := U 1
def U∞ : Type := U ∞  -- For spectra and higher structures

-- Cumulative rule
def lift (i j : Nat) (h : i ≤ j) (A : U i) : U j := A

def Set : U₀ := Set

-- Constructors
def elem (A : Set) (x : A) : A := x
def fun (A B : Set) : Set := Π (x : A), B
def lam (A B : Set) (f : A → B) : fun A B := λ (x : A), f x

-- Eliminators
def app (A B : Set) (f : fun A B) (x : A) : B := f x

-- Computation rules β and Uniqueness rules η
def β (A B : Set) (f : A → B) (x : A) : Path B (app A B (lam A B f) x) (f x) := idp B (f x)
def η (A B : Set) (f : fun A B) : Path (fun A B) f (λ (x : A), f x) := idp (fun A B) f

