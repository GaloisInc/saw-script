
>
> import Control.Comonad
>
> class Memo m where
>   check :: m e t -> t
>   lift  :: [(e, t)] -> m e t


instance Memo m e t => Comonad m e where
  extract :: m e t -> t
  extract m = check

  extend :: (m e t -> t') -> m e t -> m e t'
  extend f m = (fmap f) . duplicate $ m

> instance Memo m e t => Comonad (m ) where
>   extract m = check
>
>   extend f m = (fmap f) . duplicate $ m
>
> instance Comonad (m e) => Memo m where
>   
>




 instance Memo m e t => Comonad (m e) where
   fmap :: (t -> t') -> m e t -> m e t'
   fmap f m =
 
   extract :: m e t -> t
   extract m = 

   duplicate :: m e t -> m e (m e t)
   duplicate m =
