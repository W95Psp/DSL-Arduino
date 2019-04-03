definition module evalTask


from iTasks import always, hasValue, >>-, >>!, :: TaskValue(..), :: Task, :: Stability, :: TaskCont(..), :: Action, updateInformation, 
		viewInformation, class descr, instance descr String, :: UpdateOption, :: ViewOption(..), -||-, -&&-, -||, ||-, startEngine, 
		class Publishable, >>*, class TFunctor, instance TFunctor Task, class TApplicative, instance TApplicative Task, 
		instance Publishable Task, Void

import iTasks._Framework.Generic
import Expr

runSimulation :: (Expr a) *World -> *World | iTask a
runITaskSimulation :: (Expr a) -> (Task Void) | iTask a