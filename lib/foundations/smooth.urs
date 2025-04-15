module smooth set

def SmthSet : U₁ := Sh(CrtSp, Set)

-- Probe space
def CrtSp : U₀ := ℝ^n  -- Indexed by n : Nat

-- Constructors
def sup-plt (n q : Nat) (X : SupSmthSet) (g : Grade) : U 1 g := GradedPlt(ℝ^(n|q), X, g)
def plt (n : Nat) (X : SmthSet) : Set := Plt(ℝ^n, X)
def precomp (n m : Nat) (X : SmthSet) (f : ℝ^m → ℝ^n) (φ : plt n X) : plt m X := φ ∘ f
def glue-φ (n : Nat) (X : SmthSet) (U : OpenCover n) (φs : Π (i : I), plt (U i) X)
    (coh : Π (i j : I), Path (plt (U i ∩ U j) X) (φs i | U i ∩ U j) (φs j | U i ∩ U j))
  : plt n X := glue U φs coh

-- Derived Mapping Space
def Maps (A B : SmthSet) : SmthSet := λ (n : Nat), Π (x : plt n A), plt n B
def map (A B : SmthSet) (f : Π (n : Nat), plt n A → plt n B) : Maps A B := λ (n : Nat) (x : plt n A), f n x
def app-map (A B : SmthSet) (f : Maps A B) (n : Nat) (x : plt n A) : plt n B := f n x

-- Eliminators
def eval (n : Nat) (X : SmthSet) (φ : plt n X) : X := φ
def germ (n : Nat) (X : SmthSet) (φ : plt n X) : PltGrm(ℝ^n, X) := germ φ

-- Computation rules
def precomp-id (n : Nat) (X : SmthSet) (φ : plt n X)
OS  : Path (plt n X) (precomp n n X id φ) φ := idp (plt n X) φ
def map-β (A B : SmthSet) (f : Π (n : Nat), plt n A → plt n B) (n : Nat) (x : plt n A)
  : Path (plt n B) (app-map A B (map A B f) n x) (f n x) := idp (plt n B) (f n x)

-- Test Terms and Lemmas

-- Test 1: Smooth function as plot
def test-smooth (n m : Nat) : plt n (λ k, C^∞(ℝ^k, ℝ^m))
 := λ x, x^2  -- ℝ^n → ℝ^m, x ↦ x² (for m = 1)

def test-precomp (n m : Nat) (f : ℝ^m → ℝ^n) : plt m (λ k, C^∞(ℝ^k, ℝ^n))
 := precomp n m (λ k, C^∞(ℝ^k, ℝ^n)) f (test-smooth n n)

def test-precomp-id (n : Nat)
  : Path (plt n (λ k, C^∞(ℝ^k, ℝ^n))) (precomp n n _ id (test-smooth n n)) (test-smooth n n)
 := precomp-id n (λ k, C^∞(ℝ^k, ℝ^n)) (test-smooth n n)

-- Test 2: Mapping space
def sin-map : Maps (λ k, C^∞(ℝ^k, ℝ)) (λ k, C^∞(ℝ^k, ℝ))
 := map _ _ (λ n x, sin ∘ x)

def test-app-map (n : Nat) (φ : plt n (λ k, C^∞(ℝ^k, ℝ)))
  : plt n (λ k, C^∞(ℝ^k, ℝ)) := app-map _ _ sin-map n φ
def test-map-β (n : Nat) (φ : plt n (λ k, C^∞(ℝ^k, ℝ)))
  : Path (plt n (λ k, C^∞(ℝ^k, ℝ))) (test-app-map n φ) (sin ∘ φ)
 := map-β _ _ (λ n x, sin ∘ x) n φ

-- Lemma: Yoneda embedding (Page 2)
def yoneda (n : Nat) (X : SmthSet)
  : Path (plt n X) (Π (k : Nat), Hom_SmthSet(ℝ^k, ℝ^n) → plt k X) (λ f, precomp k n X f)
 := idp _ _  -- Reflects Hom_SmthSet(ℝ^n, X) ≅ Plt(ℝ^n, X)