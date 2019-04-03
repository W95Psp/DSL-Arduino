implementation module evalTask

import StdBool
import StdString
import StdList
import Text.JSON
import StdGeneric
import Data.Map
import iTasks._Framework.Generic
from iTasks import always, hasValue, >>-, >>!, :: TaskValue(..), :: Task, :: Stability, :: TaskCont(..), :: Action, updateInformation, 
		viewInformation, class descr, instance descr String, :: UpdateOption, :: ViewOption(..), -||-, -&&-, -||, ||-, startEngine, 
		class Publishable, >>*, class TFunctor, instance TFunctor Task, class TApplicative, instance TApplicative Task, 
		instance Publishable Task, Void
import qualified iTasks
import Data.Functor
import Control.Applicative
import Control.Monad
import _SystemArray
import lcdDescriptor
import guiArduinoSimulator

import Expr

import StdDebug

:: Result a = Result a | Fail String

:: State :== Map String Dynamic
:: Sem a = Sem (State -> (Result a, State))
instance Functor Sem where
	fmap f (Sem g) = Sem \s . case g s of
		(Result v, s) = (Result (f v), s)
		(Fail str, s) = (Fail str, s)

instance Applicative Sem where
	pure v = Sem \s . (Result v, s)
	(<*>) (Sem f) (Sem g) = Sem \s . case f s of
		(Result fun, s) = case g s of
			(Result v, s) 	= (Result (fun v), s)
			(Fail str, s) 	= (Fail str, s)
		(Fail str, s) 	= (Fail str, s)

instance Monad Sem where
	//				  f : State -> Result a
	//				  g : a -> Sem b
	bind (Sem f) g = Sem \s . case f s of
	 	(Result v, s) = case g v of
	 		Sem fun = fun s
	 	(Fail str, s)	= (Fail str, s)


fail	:: String -> Sem a
fail msg = Sem \st . (Fail msg, st)
store	:: String a -> Sem a | TC a
store i v = Sem \st.(Result v, put i (dynamic v) st)
read	:: String -> Sem a | TC a
read i = Sem \st.case get i st of
	Just (a::a^)	= (Result a, st)
	Just _			= (Fail "type error", st)
	_				= (Fail (i +++ " undefined"), st)

inverseBool :: Bool -> Bool
inverseBool True = False
inverseBool False = True

expIToSemI :: (Expr i) -> (Sem i)
expIToSemI v = eval v
storeI :: String (Sem i) -> (Sem i)  | TC i
storeI name sem = sem >>= \c . Sem \st.(Result c, put name (dynamic c) st)

class storeValuesFromTuple a
where
	storeValuesFromTuple :: a [String] -> Sem a | TC a
// instance storeValuesFromTuple Int
// where
// 	storeValuesFromTuple v [n] = return v

aTaskGetName v = case aTaskInputTypeToStringSquare v of (_,v) = v

EvalIfExpr :: (Expr Bool) (Expr a) (Expr a) -> (Sem a)
EvalIfExpr cond a b = eval cond >>= \cond . if cond (eval a) (eval b)

eval :: (Expr a) -> Sem a
eval expr = case expr of
	Integer {f} i 			= return (f i)
	Str {f} i 				= return (f i)
	Boolean 	{f} i		= return (f i)
	Str 		{f} i		= return (f i)
	Float 		{f} i		= return (f i)
	// EmptyList 	{f}			= return (f [])
	Mul 		{f} i j		= (\i j. f (i * j))			<$> eval i <*> eval j
	Div 		{f} i j		= (\i j. f (i / j))			<$> eval i <*> eval j
	Plus 		{f} i j		= (\i j. f (i + j))			<$> eval i <*> eval j
	Minus 		{f} i j		= (\i j. f (i - j))			<$> eval i <*> eval j
	Le 			{f} i j		= (\i j. f (i < j))			<$> eval i <*> eval j
	Eq 			{f} i j		= (\i j. f (i == j))		<$> eval i <*> eval j
	Not 		{f} i		= (\i . f (inverseBool i))	<$> eval i
	Or 			{f} i j		= (\i j. f (i || j))		<$> eval i <*> eval j
	And 		{f} i j		= (\i j. f (i && j))		<$> eval i <*> eval j
	Variable 		i		= read i
	// Task 		{f} name params body	= return (f {atParams = params, atBody = extractReturnedValue body})
	// RunTask		{f} exprTask exprInput	= f <$> SubRunTask exprTask exprInput
	IfExpr 		{f} cond a b 			= f <$> EvalIfExpr cond a b
	IfRetV 		{f} cond (ReturnedValue a) (ReturnedValue b) = f <$> (EvalIfExpr cond a b)
	Tuple2 		{f}	(b,c)		= (\b c . 		f (b, c)) 	<$> eval b <*> eval c
	Tuple3 		{f}	(b,c,d)		= (\(b,c) d . f(b,c,d)) <$>
											((\b c . (b, c)) <$> eval b <*> eval c)
										<*> eval d
	Tuple4 		{f}	(b,c,d,e)	= (\(b,c) (d,e) . f(b,c,d,e)) <$>
											((\b c . (b, c)) <$> eval b <*> eval c)
										<*> ((\b c . (b, c)) <$> eval d <*> eval e)
	Tuple5 		{f}	(b,c,d,e,j)	= (\(b,c,d,e) j . f (b,c,d,e,j)) <$> (
										(\(b,c) (d,e) . (b,c,d,e)) <$>
												((\b c . (b, c)) <$> eval b <*> eval c)
											<*> ((\b c . (b, c)) <$> eval d <*> eval e)
									) <*> eval j

	// GetTimestamp {f} 			= f <$>  
	// ComposeTasks	(BM a (ATask (i1,i2) (o1,o2)))	CmpTasks (ATask i1 o1) (ATask i2 o2)
	// ComposeTasks {f} how (ATask i1 o1) 
	// BindTasks		(BM a (ATask i1 o2))			(ATask i1 o1) (ATask o1 o2)
	// BindTasks		(BM a (ATask i1 o2))			(ATask i1 o1) (ATask o1 o2)


derive class iTask ATaskInputType
derive class iTask ATask

// derive class iTask ATask

extractReturnedValueTask :: (ReturnedValue (Expr a)) -> (Expr a) | iTask a
extractReturnedValueTask (ReturnedValue v) = v

// ExecTTask (Task _ name params body) vars = ExecTask name params body

ExecTask :: String [ATaskInputType] (ReturnedValue (Expr o)) (Map String Dynamic) -> (Task o) | iTask o
ExecTask name params body vars = evalTask (extractReturnedValueTask body) vars

// DoTask :: String [ATaskInputType] (ReturnedValue (Expr o)) (Map String Dynamic) -> (Task (ATask i o)) | iTask o
// DoTask name params body vars = evalTask (extractReturnedValueTask body) vars >>>= \body . treturn ( {atParams = params, atBody = body})

fetchInVars	:: String (Map String Dynamic) -> Task a | iTask a & TC a
fetchInVars i st = case get i st of
	Just (a::a^)	= treturn a
		where
			dr = toString (typeCodeOfDynamic (dynamic a))
	Just r			= trace ("\n\n{{ErrorEvalTask:Error of type with variable "+++ i +++" of type "+++ dr +++"}}\n\n") throw ("Error fetching variable " +++ i)
		where
			dr = toString (typeCodeOfDynamic r)
	_ 				= trace ("\n\n{{ErrorEvalTask:Error fetching variable "+++ i +++"}}\n\n") throw ("Error fetching variable " +++ i)


class storeDInMap a
where
	storeDInMap :: [String] a (Map String Dynamic) -> (Map String Dynamic) | TC a & iTask a

instance storeDInMap (a, b) | TC a & TC b & iTask a & iTask b
where
	storeDInMap [t,u] (a,b) st = put t (dynamic a) (put u (dynamic b) st) 

instance storeDInMap a
where
	storeDInMap [t] a st = put t (dynamic a) st 

// instance storeDInMap (Task (a, b, c)) | TC a & iTask a & TC b & iTask b & TC c & iTask c
// where
// 	storeDInMap [t,u,v] d st = d >>>= \(a,b,c) .treturn (put t (dynamic a) (put u (dynamic b) (put v (dynamic c) st))) 

storeDynamic :: [String] Dynamic (Map String Dynamic) -> (Map String Dynamic)
storeDynamic [t,u] ((a,b) :: (a,b)) st = put t (dynamic a) (put u (dynamic b) st)
storeDynamic [t,u,v] ((a,b,c) :: (a,b,c)) st = put t (dynamic a) (put u (dynamic b) (put v (dynamic c) st))
storeDynamic [t,u,v,w] ((a,b,c,d) :: (a,b,c,d)) st = put t (dynamic a) (put u (dynamic b) (put v (dynamic c) (put w (dynamic d) st)))
storeDynamic [t,u,v,w,x] ((a,b,c,d,e) :: (a,b,c,d,e)) st = put t (dynamic a) (put u (dynamic b) (put v (dynamic c) (put w (dynamic d) (put x (dynamic e) st))))
storeDynamic [n] any st = put n any st

storeInMap :: [String] (Expr a) (Map String Dynamic) -> (Task (Map String Dynamic)) | TC a & iTask a
storeInMap tab t st = doit <<$>> evalTask t st
where
	doit val = storeDynamic tab (dynamic val) st
// storeInMap tab (RunTask bmFun task inp) st = doit <<$>> evalTask t st
// where
// 	doit val = storeDynamic tab (dynamic val) st
// 	t = (RunTask bmFun task inp)
// storeInMap [name] (RunTask bmFun task inp) st = (\(val,b) . put name (dynamic val) st) <<$>> evalTask (RunTask bmFun task inp) st
storeInMap [t,u] 		(Tuple2 _ (a,b)) 		st = ((\a b . put t (dynamic a) (put u (dynamic b) st))
				<<$>> evalTask a st) <<*>> evalTask b st
storeInMap [t,u,v] 		(Tuple3 _ (a,b,c)) 		st = (((\a b c. put t (dynamic a) (put u (dynamic b) (put v (dynamic c) st)))
				<<$>> evalTask a st) <<*>> evalTask b st) <<*>> evalTask c st
storeInMap [t,u,v,w] 	(Tuple4 _ (a,b,c,d)) 	st = ((((\a b c d. put t (dynamic a) (put u (dynamic b) (put v (dynamic c) (put w (dynamic d) st))))
				<<$>> evalTask a st) <<*>> evalTask b st) <<*>> evalTask c st) <<*>> evalTask d st
storeInMap [t,u,v,w,x] 	(Tuple5 _ (a,b,c,d,e)) 	st = (((((\a b c d e. put t (dynamic a) (put u (dynamic b) (put v (dynamic c) (put w (dynamic d) (put x (dynamic e) st)))))
				<<$>> evalTask a st) <<*>> evalTask b st) <<*>> evalTask c st) <<*>> evalTask d st) <<*>> evalTask e st
storeInMap [name] val 							st =
		(\val . put name (dynamic val) st) <<$>> evalTask val st
storeInMap _ val _ = trace ("\n\n{{ErrorEvalTask:Incorrect number of parameters, value is of type "+++ddd+++"}}\n\n") throw "Incorrect number of parameters"
where
	ddd = toString (typeCodeOfDynamic (dynamic val))


EvalIfExprTask :: (Expr Bool) (Expr a) (Expr a) (Map String Dynamic) -> (Task a) | iTask a
EvalIfExprTask cond a b vars = evalTask cond vars >>>= \cond . if cond (evalTask a vars) (evalTask b vars)

RunTaskRoutine :: (Expr (ATask i o)) (Expr i) (Map String Dynamic) -> (Task o) | TC i & iTask i & iTask o
RunTaskRoutine task input vars = (\(ATask v) . v) <<$>> (
							storeInMap params input vars >>>= \vars . evalTask task vars
						)
	where
		params = map aTaskGetName case task of (Task _ _ v _) = v

// RunTaskRoutineDirect :: (Expr (ATask i o)) (Expr i) (Map String Dynamic) -> (Task o) | TC i & iTask i & iTask o
// RunTaskRoutineNul task input vars = (\(ATask v) . v) <<$>> (
// 			storeInMap ["sad"] input vars >>>= \vars . evalTask task vars
// 		)


evalTask :: (Expr a) (Map String Dynamic) -> (Task a) | iTask a & TC a
evalTask expr vars = case expr of
	Integer {f} i 			= treturn (f i)
	Str {f} i 				= treturn (f i)
	Boolean 	{f} i		= treturn (f i)
	Str 		{f} i		= treturn (f i)
	Float 		{f} i		= treturn (f i)
	Mul 		{f} i j		= ((\i j. f (i * j))			<<$>> evalTask i vars) <<*>> evalTask j vars
	Div 		{f} i j		= ((\i j. f (i / j))			<<$>> evalTask i vars) <<*>> evalTask j vars
	Plus 		{f} i j		= ((\i j. f (i + j))			<<$>> evalTask i vars) <<*>> evalTask j vars
	Minus 		{f} i j		= ((\i j. f (i - j))			<<$>> evalTask i vars) <<*>> evalTask j vars
	Le 			{f} i j		= ((\i j. f (i < j))			<<$>> evalTask i vars) <<*>> evalTask j vars
	Eq 			{f} i j		= ((\i j. f (i == j))			<<$>> evalTask i vars) <<*>> evalTask j vars
	Not 		{f} i 		= ((\i. f (inverseBool i))		<<$>> evalTask i vars)
	Or 			{f} i j		= ((\i j. f (i || j))			<<$>> evalTask i vars) <<*>> evalTask j vars
	And 		{f} i j		= ((\i j. f (i && j))			<<$>> evalTask i vars) <<*>> evalTask j vars
	Task 		{f} name params body	= ExecTask name params body vars >>>= \v . treturn (f (ATask v))
	RunTask 	{f} task input = f <<$>> (RunTaskRoutine task input vars)
	where
		taskN = case task of (Task _ n _ _)=n
	GetFstTuple2{f} t		= f <<$>> (ret <<$>> data)
	where
		// data :: Task (tt1, tt2)
		data = evalTask t vars
		ret :: (t1, t2) -> t1 | iTask t1 & TC t1 & iTask t2 & TC t2 
		ret z = case z of
			(a,b) = a
	GetSndTuple2{f} t		= (\(_,b). f b)		<<$>> evalTask t vars
	Tuple2 		{f}	(b,c)		= ((\b c . 		f (b, c)) 	<<$>> evalTask b vars) <<*>> evalTask c vars
	Tuple3 		{f}	(b,c,d)		= ((\(b,c) d . f(b,c,d)) <<$>>
												(((\b c . (b, c)) <<$>> evalTask b vars) <<*>> evalTask c vars))
											<<*>> evalTask d vars
	Tuple4 		{f}	(b,c,d,e)	= ((\(b,c) (d,e) . f(b,c,d,e)) <<$>>
												(((\b c . (b, c)) <<$>> evalTask b vars) <<*>> evalTask c vars))
										<<*>> (((\b c . (b, c)) <<$>> evalTask d vars) <<*>> evalTask e vars)
	Tuple5 		{f}	(b,c,d,e,j)	= ((\(b,c,d,e) j . f (b,c,d,e,j)) <<$>> (
											((\(b,c) (d,e) . (b,c,d,e)) <<$>>
												(((\b c . (b, c)) <<$>> evalTask b vars) <<*>> evalTask c vars))
												<<*>> (((\b c . (b, c)) <<$>> evalTask d vars) <<*>> evalTask e vars)
										)) <<*>> evalTask j vars
	Variable 		i		= fetchInVars i vars

	IfExpr 		{f} cond a b 			= f <<$>> EvalIfExprTask cond a b vars
	IfRetV 		{f} cond (ReturnedValue a) (ReturnedValue b)
										= f <<$>> EvalIfExprTask cond a b vars	
	// ComposeExpr {f} (ReturnedValue a) (ReturnedValue b)
	// 									= f <<$>> (evalTask a vars >>>| evalTask b vars)
	GetTimestamp{f}			= 
							('iTasks'.get 'iTasks'.currentTimestamp) 
								>>- \('iTasks'.Timestamp n) .
									'iTasks'.wait " " (\('iTasks'.Timestamp nn) . nn > n) ('iTasks'.currentTimestamp) >>>= \('iTasks'.Timestamp n) . treturn (f n)
	// GetTimestamp{f}			= ('iTasks'.get 'iTasks'.currentTimestamp) >>- \('iTasks'.Timestamp n) . treturn (f (trace ("\ncurrent time = "+++(toString n)+++" \n") n))
	GetButtonPressed{f}		= ('iTasks'.get lcdState) >>- \s . ('iTasks'.upd (\s . {s & ldEvent = 0}) lcdState) >>>| treturn (f s.ldEvent)
	Clear 		{f}			= ('iTasks'.upd (\s . {s & ldLine2 = ""}) lcdState) >>>| treturn (f Void)
	RunTasksSequence	{f}	a b	i	= f <<$>> (RunTasksSequenceFun a b i vars)
	RunTasksSeqRedirect	{f}	a b	ia ib fr= f <<$>> (RunTasksSeqRedirFun a b ia ib fr vars)
	RunTasksKeepBoth	{f}	a b	i	= f <<$>> (RunTasksKeepBothFun a b i vars)
	RunTasksKeepAny		{f}	a b	i	= f <<$>> (RunTasksKeepAnyFun a b i vars)
	RunTasksKeepLeft	{f}	a b	i	= f <<$>> (RunTasksKeepLeftFun a b i vars)
	WaitForButton{f} button state = f <<$>>
				(
					evalTask state vars >>>= \state . 
					(
						evalTask button vars >>>= \button . 
							(
								'iTasks'.wait " " (\s . case state of
									True = button == s.ldEvent
									False = button == 0
								) lcdState >>>| (
									'iTasks'.upd (\s . {s & ldEvent = 0}) lcdState
									>>>| treturn Void
								)
							)
					)
				)
	GetButtonPressedBlocking{f} = f <<$>> (
					'iTasks'.wait " " (\s . s.ldEvent > 0) lcdState >>>= \st . (
						'iTasks'.upd (\s . {s & ldEvent = 0}) lcdState
						>>>| treturn st.ldEvent
					)
				)
	// WaitForButton{f} button state = 'iTasks'.get lcdState >>>= \s . if (s==state) Void (wait  )
	Print 		{f} s l t 		= f <<$>> (evalTask s vars >>>= \s . evalTask l vars >>>= \l . evalTask t vars >>>= \t . ('iTasks'.upd case t of
				0 = \x . {x & ldLine1 = WriteOnLine x.ldLine1 s l}
				_ = \x . {x & ldLine2 = WriteOnLine x.ldLine2 s l}
			 lcdState) >>>| treturn Void)
	VoidExpr	{f} = treturn (f Void)
	ToString	{f} v = (\v . f (toString v)) <<$>> evalTask v vars
	ConcatSTR	{f} a b = ((\v w . f ((toString v) +++ (toString w))) <<$>> evalTask a vars) <<*>> evalTask b vars

// RunTasksKeepLeftFun :: (BM a o) (Expr (ATask i p)) (Expr (ATask p o)) (Expr i) -> (Task o) | TC i & iTask p & iTask o
// RunTasksKeepLeftFun {f} a b input = execFirst input >>>=
// 	where
// 		execFirst	:: (Expr i) -> (Task p)
// 		execFirst	i = evalTask (RunTask bm a i) vars
// 		execSecond	:: (Expr p) -> (Task o)
// 		execSecond	i = evalTask (RunTask bm b i) vars
RunTasksKeepLeftFun :: (Expr (ATask i o)) (Expr (ATask i p)) (Expr i) (Map String Dynamic) -> (Task o) | TC i & iTask p & iTask o & iTask i
RunTasksKeepLeftFun a b i vars = (evalTask (RunTask bm a i) vars) -|| (evalTask (RunTask bm b i) vars)

RunTasksSequenceFun :: (Expr (ATask i p)) (Expr (ATask p o)) (Expr i) (Map String Dynamic) -> (Task o) | TC i & TC p & iTask p & iTask o & iTask i
RunTasksSequenceFun a b input vars = evalTask (RunTask bm b (RunTask bm a input)) vars

// class liftInExpr a
// liftInExpr a -> (Expr a)


RunTasksSeqRedirFun :: (Expr (ATask i z)) (Expr (ATask p o)) (Expr i) (Expr y) (Expr (ATask (z,y) p)) (Map String Dynamic) -> (Task o) | TC i & TC p & TC z & TC y & iTask p & iTask z & iTask o & iTask i & iTask y
// RunTasksSeqRedirFun a b ia ib vars = (evalTask (RunTask bm a ia) vars) >>- \_ . (evalTask (task  b) vars)
RunTasksSeqRedirFun a b ia ib f vars = evalTask tb vars
	where
		tf = RunTask bm f (Tuple2 bm (ta, ib))
		ta = RunTask bm a ia
		tb = RunTask bm b tf


// runSubTask :: (Expr (ATask input output)) input -> (Expr output) | TC output & TC input & iTask output & iTask input
// runSubTask f input = RunTask bm f input

// makeTuple2 :: (output) (input) -> Expr (output, input) | TC output & TC input & iTask output & iTask input
// makeTuple2 output input = tuple2 (output, input)
// RunTasksSeqRedirFun a b ia ib vars = (evalTask (RunTask bm a ia) vars) >>- \_ . (RunTaskRoutineNul b ib vars)

RunTasksKeepBothFun :: (Expr (ATask i o)) (Expr (ATask i p)) (Expr i) (Map String Dynamic) -> (Task (o,p)) | TC i & iTask p & iTask o & iTask i
RunTasksKeepBothFun a b i vars = (evalTask (RunTask bm a i) vars) -&&- (evalTask (RunTask bm b i) vars)

RunTasksKeepAnyFun :: (Expr (ATask i o)) (Expr (ATask i o)) (Expr i) (Map String Dynamic) -> (Task o) | TC i & iTask o & iTask i
RunTasksKeepAnyFun a b i vars = (evalTask (RunTask bm a i) vars) -||- (evalTask (RunTask bm b i) vars)



(>>>=)     :== 'iTasks'.tbind
(>>>|) a b :== 'iTasks'.tbind a (\_ -> b)
treturn    :== 'iTasks'.return
throw    :== 'iTasks'.throw
ActionOk   :== 'iTasks'.ActionOk
ActionQuit :== 'iTasks'.ActionQuit
ActionNew  :== 'iTasks'.ActionNew

(<<$>>) :== 'iTasks'.tmap
(<<*>>) a b = a >>>= \f -> 'iTasks'.tmap f b

blankLine = "                "
// lcdState :: 'iTasks'.ReadWriteShared LcdDescriptor LcdDescriptor
lcdState = 'iTasks'.sharedStore "lcdState" emptyLcdState  
emptyLcdState = {ldLine1 = blankLine, ldLine2 = blankLine, ldEvent = 0}

subString start len haystack = haystack % (start, start + len - 1)

WriteOnLine :: String String Int -> String
WriteOnLine line text givenStart
		| givenStart >= sLine = line
		| givenStart + sText >= sLine = (subString 0 givenStart line) +++ txt
		| givenStart + sText < sLine  = (subString 0 givenStart line) +++ txt +++ (subString (givenStart + sText) sLine line)
	where
		txt   = if (givenStart + sText > sLine) (subString 0 (sLine - givenStart) text) text
		sLine = size line
		sText = size text

// LcdDescriptor_write :: Int Int String
// LcdDescriptor_write left top str = 

// Start :: *World -> *World
// Start world = runSimulation (bb1) world

// displayLcd :: LcdDescriptor -> Image LcdDescriptor
// displayLcd descriptor = 'iTasks'.circle ('iTasks'.px 20)

// imageTask :: Task LcdDescriptor
// imageTask =
// 	updateSharedInformation (Title "Arduino Simulation")
// 		[imageUpdate
// 			id							// server state (share) and view are identical
// 			(\s v tags -> displayLcd s)
// 										// generate image
// 			(\s v -> v)					// update view when state changes
// 			(\s v -> s)					// update state when view changes
// 			(\_ s -> Nothing)			// no conflict handling
// 			(\o n.n)					// always select the new state
// 		]
// 		state

showLcd :: (Task Void)
showLcd = (imageTask lcdState) >>>| showLcd

runSimulation :: (Expr a) *World -> *World | iTask a
runSimulation expr world = startEngine (runITaskSimulation expr) world

runITaskSimulation :: (Expr a) -> (Task Void) | iTask a
runITaskSimulation t = ('iTasks'.set emptyLcdState lcdState) >>>| (showLcd -|| (evalTask t Tip))