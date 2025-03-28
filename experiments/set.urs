def Set : U₀ := Set

-- Constructors
def elem (A : Set) (x : A) : A := x
def fun (A B : Set) : Set := Π (x : A), B
def lam (A B : Set) (f : A → B) : fun A B := λ (x : A), f x

-- Eliminators
def app (A B : Set) (f : fun A B) (x : A) : B := f x

-- Computation rules
def β (A B : Set) (f : A → B) (x : A) : Path B (app A B (lam A B f) x) (f x) := idp B (f x)
def η (A B : Set) (f : fun A B) : Path (fun A B) f (λ (x : A), f x) := idp (fun A B) f
