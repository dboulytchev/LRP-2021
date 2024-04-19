{-# LANGUAGE GHC2021, UndecidableInstances #-}

module Fix where


newtype Fix f = In { out :: f (Fix f) }

deriving instance Show (f (Fix f)) => Show (Fix f)
deriving instance Read (f (Fix f)) => Read (Fix f)
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Ord (f (Fix f)) => Ord (Fix f)

type Algebra f a = f a -> a
type Coalgebra f a = a -> f a


cata :: Functor f => Algebra f a -> Fix f -> a
cata phi (In x) = phi $ cata phi <$> x

ana :: Functor f => Coalgebra f a -> a -> Fix f
ana psi x = In $ ana psi <$> psi x

hylo :: Functor f => Algebra f b -> Coalgebra f a -> a -> b
hylo phi psi = cata phi . ana psi
