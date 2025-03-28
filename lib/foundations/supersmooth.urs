module supersmooth where

def SupSmthSet : U₁ := Sh(SupCrtSp, Set)

-- Super probe space
def SupCrtSp : U₀ := ℝ^(n|q)  -- Indexed by (n, q : Nat)

-- Constructors
def sup-plt (n q : Nat) (X : SupSmthSet) : Set := Plt(ℝ^(n|q), X)
def sup-precomp (n q m r : Nat) (X : SupSmthSet) (f : ℝ^(m|r) → ℝ^(n|q)) (φ : sup-plt n q X)
  : sup-plt m r X := φ ∘ f
def sup-glue (n q : Nat) (X : SupSmthSet) (U : OpenCover n) (φs : Π (i : I), sup-plt (U i) q X)
    (coh : Π (i j : I), Path (sup-plt (U i ∩ U j) q X) (φs i | U i ∩ U j) (φs j | U i ∩ U j))
  : sup-plt n q X := glue U φs coh

-- Derived Mapping Space
def Maps (A B : SupSmthSet) : SupSmthSet := λ (n q : Nat), Π (x : sup-plt n q A), sup-plt n q B
def map (A B : SupSmthSet) (f : Π (n q : Nat), sup-plt n q A → sup-plt n q B) : Maps A B
 := λ (n q : Nat) (x : sup-plt n q A), f n q x
def app-map (A B : SupSmthSet) (f : Maps A B) (n q : Nat) (x : sup-plt n q A) : sup-plt n q B := f n q x

-- Eliminators
def bosonic (n q : Nat) (X : SupSmthSet) (φ : sup-plt n q X) : plt n X := φ.1
def fermionic (n q : Nat) (X : SupSmthSet) (φ : sup-plt n q X) : ∧^q (ℝ^q)* → X := φ.2

-- Computation rules
def sup-precomp-id (n q : Nat) (X : SupSmthSet) (φ : sup-plt n q X)
  : Path (sup-plt n q X) (sup-precomp n q n q X id φ) φ := idp (sup-plt n q X) φ
def sup-map-β (A B : SupSmthSet) (f : Π (n q : Nat), sup-plt n q A → sup-plt n q B) (n q : Nat) (x : sup-plt n q A)
  : Path (sup-plt n q B) (app-map A B (map A B f) n q x) (f n q x) := idp (sup-plt n q B) (f n q x)

-- Test Terms and Lemmas

-- Test 1: Super plot with fermionic coordinate
def test-super (X : SupSmthSet) : sup-plt 1 1 X := λ (x, θ), x + θ  -- θ² = 0
def test-super-precomp (m r : Nat) (X : SupSmthSet) (f : ℝ^(m|r) → ℝ^(1|1))
  : sup-plt m r X := sup-precomp 1 1 m r X f (test-super X)
def test-super-id (X : SupSmthSet)
  : Path (sup-plt 1 1 X) (sup-precomp 1 1 1 1 X id (test-super X)) (test-super X)
 := sup-precomp-id 1 1 X (test-super X)

-- Test 2: Bosonic and fermionic components
def test-bosonic (X : SupSmthSet) : plt 1 X := bosonic 1 1 X (test-super X)
def test-fermionic (X : SupSmthSet) : ∧^1 (ℝ^1)* → X := fermionic 1 1 X (test-super X)

-- Lemma: Spinor fields (Page 6)
def spinor-map (S : SpinorBundle) : Maps (ΠS) (λ k, C^∞(ℝ^k, ℝ))
 := map _ _ (λ n q φ, λ x, φ x)  -- Maps from super smooth set ΠS to smooth ℝ-valued functions

