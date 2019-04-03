implementation module Expr

import StdBool
import StdString
import StdDynamic
import StdList
import iTasks._Framework.Generic

instance == ATaskInputType
where
	(==) (AtInt a) (AtInt b) = a==b
	(==) (AtFloat a) (AtFloat b) = a==b
	(==) (AtBoolean a) (AtBoolean b) = a==b
	(==) (AtString a) (AtString b) = a==b
	(==) (AtList a) (AtList b) = a==b

instance toString ATaskInputType
where
	toString (AtInt _) 		= "int"
	toString (AtString _) 	= "string"
	toString (AtBoolean _) 	= "int"
	toString (AtList v) 	= "case v of"
	toString (AtList v) 	= case v of
		(AtList v)	= (toString v) +++ "*"
		_ 			= (toString v) +++ " *"


aTaskInputTypeGetFinalString (AtList v) = aTaskInputTypeGetFinalString v
aTaskInputTypeGetFinalString v = case aTaskInputTypeToStringSquare v of
			(_,str) = str

aTaskInputTypeToStringSquare :: ATaskInputType -> (String, String)
aTaskInputTypeToStringSquare (AtInt v) = (toString (AtInt v), v)
aTaskInputTypeToStringSquare (AtFloat v) = (toString (AtFloat v), v)
aTaskInputTypeToStringSquare (AtBoolean v) = (toString (AtBoolean v), v)
aTaskInputTypeToStringSquare (AtString v) = (toString (AtString v), v)
aTaskInputTypeToStringSquare (AtList v) = (toString (AtList v), aTaskInputTypeGetFinalString v)

:: ATaskInputType = AtInt String | AtFloat String | AtBoolean String | AtString String | AtList ATaskInputType
:: BM a b = { t :: a -> b, f :: b -> a }
id :: a -> a
id a = a
bm :: BM a a
bm = {f = id, t = id}


:: ATask tIn tOut = ATask tOut
:: PossibleButtons	= LDE_Nothing | LDE_bLeft | LDE_bRight | LDE_bDown | LDE_bUp | LDE_bSelect | LDE_Any

:: ReturnedValue a = ReturnedValue a
:: Expr a
	= 			Integer (BM a Int) Int
	| 			Boolean (BM a Bool) Bool
	| 			Str (BM a String) String
	| 			Float (BM a Real) Real
	| 			VoidExpr (BM a Void)
//	| E.b:		EmptyList (BM a b) 											& toString b
//	| E.b:		AddList (BM a b) (Expr b) (Expr [b])						& toString b
//	| E.b:		Length (BM a Int) (Expr [b])								& toString b
	| E.b:		Mul (BM a b) (Expr b) (Expr b)								& * b & iTask b 
	| E.b:		Div (BM a b) (Expr b) (Expr b)								& / b & iTask b
	| E.b:		Plus (BM a b) (Expr b) (Expr b)								& + b & iTask b
	| E.b:		Minus (BM a b) (Expr b) (Expr b)							& - b & iTask b
	| E.b:		Le  (BM a Bool) (Expr b) (Expr b)							& Ord b & iTask b
	| E.b:		Eq  (BM a Bool) (Expr b) (Expr b)							& Eq b & iTask b
	| 			Not (BM a Bool) (Expr Bool)
	| 			Or  (BM a Bool) (Expr Bool) (Expr Bool)
	| 			And  (BM a Bool) (Expr Bool) (Expr Bool)
	| E.i o:	Task (BM a (ATask i o)) String [ATaskInputType] (ReturnedValue (Expr o)) 				& TC i & iTask i & iTask o
	| E.i o z:	RunTasksKeepLeft (BM a o) 		(Expr (ATask i o)) (Expr (ATask i z)) (Expr i)			& TC i & iTask i & iTask o & iTask z
	| E.i o p:	RunTasksKeepBoth (BM a (o,p)) 	(Expr (ATask i o)) (Expr (ATask i p)) (Expr i)			& TC i & iTask i & iTask o & iTask p
	| E.i o:	RunTasksKeepAny  (BM a o) 		(Expr (ATask i o)) (Expr (ATask i o)) (Expr i)			& TC i & iTask i & iTask o
	| E.i o p:	RunTasksSequence (BM a o) 		(Expr (ATask i p)) (Expr (ATask p o)) (Expr i)			& TC i & TC p & iTask i & iTask o & iTask p
	| E.i o p z y:RunTasksSeqRedirect (BM a o)	(Expr (ATask i z)) (Expr (ATask p o)) (Expr i) (Expr y) (Expr (ATask (z, y) p))	& TC i & TC z & TC y & TC p & iTask i & iTask o & iTask z & iTask p & iTask y
	| E.i o:	RunTask (BM a o) (Expr (ATask i o)) (Expr i)											& TC i & iTask i & iTask o & TC o
	| E.i1 i2 o1 o2:	CompWaitLeft	(BM a (ATask (i1,i2) o1))		(ATask i1 o1) (ATask i2 o2)
	| E.i1 i2 o:		CompWaitAny		(BM a (ATask (i1,i2) o))		(ATask i1 o) (ATask i2 o)
	| E.i1 i2 o1 o2:	CompWaitBoth	(BM a (ATask (i1,i2) (o1,o2)))	(ATask i1 o1) (ATask i2 o2)
	| E.i1 o1 o2:		BindTasks		(BM a (ATask i1 o2))			(ATask i1 o1) (ATask o1 o2)
	| E.b c: 		GetFstTuple2 (BM a b)	(Expr (b,c)) 			& TC b & TC c & iTask c & iTask b
	| E.b c: 		GetSndTuple2 (BM a c)	(Expr (b,c)) 			& TC b & TC c & iTask c & iTask b
	| E.b c:		Tuple2 (BM a (b,c))			(Expr b,Expr c)							& TC b & iTask b & TC c & iTask c
	| E.b c d:		Tuple3 (BM a (b,c,d))		(Expr b,Expr c,Expr d)					& TC b & iTask b & TC c & iTask c & TC d & iTask d
	| E.b c d e:	Tuple4 (BM a (b,c,d,e))		(Expr b,Expr c,Expr d,Expr e)			& TC b & iTask b & TC c & iTask c & TC d & iTask d & TC e & iTask e
	| E.b c d e f:	Tuple5 (BM a (b,c,d,e,f))	(Expr b,Expr c,Expr d,Expr e,Expr f)	& TC b & iTask b & TC c & iTask c & TC d & iTask d & TC e & iTask e & TC f & iTask f
	| E.o:			IfExpr (BM a o) (Expr Bool) (Expr o) (Expr o)									& iTask o
	| E.o:			IfRetV (BM a o) (Expr Bool) (ReturnedValue (Expr o)) (ReturnedValue (Expr o))	& iTask o
	| Variable String & TC a
// | E.o1 o2:	ComposeExpr 	(BM a o2) (ReturnedValue (Expr o1)) (ReturnedValue (Expr o2))		& iTask o1 & iTask o2
	| 			GetTimestamp (BM a Int)
	| 			Clear (BM a Void)
	| 			Print (BM a Void) (Expr String) (Expr Int) (Expr Int)
	| 			WaitForButton (BM a Void) (Expr Int) (Expr Bool)
	| 			GetButtonPressedBlocking (BM a Int)
	| 			GetButtonPressed (BM a Int)
	| E.b:		ToString (BM a String) (Expr b)								& toString b & iTask b
	| E.b c:	ConcatSTR (BM a String) (Expr b) (Expr c)					& toString b & iTask b & toString c & iTask c
// bindTasks (Task _ nameA paramsA bodyA) (Task _ nameB paramsB bodyB) = task ("bind::" +++ nameA +++ ":" +++ nameB)
(++.) infixl 4:: (Expr b) (Expr c) -> (Expr String) | toString b & iTask b & toString c & iTask c
(++.) a b = ConcatSTR bm a b

integer 		:: (Int -> (Expr Int))
integer 		= Integer bm
boolean 		:: (Bool -> (Expr Bool))
boolean 		= Boolean bm
str 			:: (String -> (Expr String))
str 			= Str bm
float 			:: (Real -> (Expr Real))
float 			= Float bm
(*.) 	infixl 7:: ((Expr b) (Expr b) -> (Expr b)) | * b & iTask b
(*.) 			= Mul bm
(/.) 	infixl 7:: ((Expr b) (Expr b) -> (Expr b)) | / b & iTask b
(/.) 			= Div bm
(+.) 	infixl 6:: ((Expr b) (Expr b) -> (Expr b)) | + b & iTask b
(+.) 			= Plus bm
(-.) 	infixl 6:: ((Expr b) (Expr b) -> (Expr b)) | - b & iTask b
(-.) 			= Minus bm
(&&.)	infixl 3:: ((Expr Bool) (Expr Bool) -> (Expr Bool))
(&&.) 			= (And bm)
(||.)	infixl 3:: ((Expr Bool) (Expr Bool) -> (Expr Bool))
(||.) 			= (Or bm)
(<.)	infixl 4:: ((Expr b) (Expr b) -> (Expr Bool)) | Ord b & iTask b
(<.)			= (Le bm)
(<=.)	infixl 4:: (Expr b) (Expr b) -> (Expr Bool) | Ord b & Eq b & iTask b
(<=.) a b 		= (a <. b) ||. (a ==. b)
notExpr			:: ((Expr Bool) -> (Expr Bool))
notExpr			= (Not bm)
(>=.)	infixl 4:: (Expr b) (Expr b) -> (Expr Bool) | Ord b & Eq b & iTask b
(>=.) a b 		= notExpr (a <. b)
(>.)	infixl 4:: (Expr b) (Expr b) -> (Expr Bool) | Ord b & Eq b & iTask b
(>.) a b 		= notExpr (a <=. b)
(==.)	infixl 4:: ((Expr b) (Expr b) -> (Expr Bool)) | Ord b & Eq b & iTask b
(==.) 			= (Eq bm)
(!=.)	infixl 4:: (Expr b) (Expr b) -> (Expr Bool) | Ord b & Eq b & iTask b
(!=.) a b		= notExpr (a ==. b)
variable 		:: (String -> (Expr a)) | TC a
variable 		= Variable
tuple2 			:: ((Expr b, Expr c) 						 -> (Expr (b,c)))		| TC b & iTask b & TC c & iTask c
tuple2 			= (Tuple2 bm)
tuple3 			:: ((Expr b, Expr c, Expr d) 				 -> (Expr (b,c,d)))		| TC b & iTask b & TC c & iTask c & TC d & iTask d
tuple3 			= (Tuple3 bm)
tuple4 			:: ((Expr b, Expr c, Expr d, Expr e) 		 -> (Expr (b,c,d,e)))	| TC b & iTask b & TC c & iTask c & TC d & iTask d & TC e & iTask e
tuple4 			= (Tuple4 bm)
tuple5 			:: ((Expr b, Expr c, Expr d, Expr e, Expr f) -> (Expr (b,c,d,e,f))) | TC b & iTask b & TC c & iTask c & TC d & iTask d & TC e & iTask e & TC f & iTask f
tuple5 			= (Tuple5 bm)
getTimestamp	:: (Expr Int)
getTimestamp 	= (GetTimestamp bm)
getButtonPressed:: (Expr Int)
getButtonPressed= (GetButtonPressed bm)



runTask 		:: (Expr (ATask i o)) (Expr i) -> (ReturnedValue (Expr o))			| TC i & iTask i & iTask o
runTask a b = ReturnedValue (RunTask bm a b) 
(:=.) infixr 9 :: ((ReturnedValue (Expr o)) -> (Expr (ATask i o))) (Expr o) -> (Expr (ATask i o))
(:=.) fun exp = fun (ReturnedValue (exp))
print 			:: ((Expr String) (Expr Int) (Expr Int) -> (Expr Void))
print 			=  (Print bm)
stringFrom		:: ((Expr b) -> (Expr String)) | toString b & iTask b
stringFrom 		= (ToString bm)

task 			:: (String [ATaskInputType] (ReturnedValue (Expr o)) -> (Expr (ATask i o))) | TC i & iTask i & iTask o
task 			= Task bm

gFst :: ((Expr (b, c)) -> (Expr b))		| TC b & TC c & iTask c & iTask b
gFst = (GetFstTuple2 bm)
gSnd :: ((Expr (b, c)) -> (Expr c)) 		| TC b & TC c & iTask c & iTask b
gSnd = (GetSndTuple2 bm)

// mkTask :: String [ATaskInputType] (ReturnedValue (Expr o)) -> ((Expr i) -> (ReturnedValue (Expr o))) | TC i & iTask i & iTask o
// mkTask id params body = call
// where
// 	call input = runTask (task id params body) input



// (>>=.) infixl 1 :: (ATask i p) (ATask p o) -> (i(Expr o)) | TC i & TC p & iTask i & iTask o & iTask p
// (>>=.) a b = task (an +++ " >>=. " +++ bn) ap ((runTasksSequence a b))
// where
// 	an = case a of (Task _ n _ _) = n
// 	ap = case a of (Task _ _ n _) = n
// 	bn = case b of (Task _ n _ _) = n

// class mkTask a
// where
// 	mkTask :: a [String] -> (i -> (Expr (ATask i o))))
// instance If (Expr a) | iTask a
// where
// 	If cond ba bb = IfExpr bm cond ba bb
// instance If (ReturnedValue (Expr a)) | iTask a
// where
// 	If cond ba bb = ReturnedValue (IfRetV bm cond ba bb)

// class findATaskInputTypeFromType a
// where
	// findATaskInputTypeFromType :: (Maybe a) ->  

runTasksSequence :: ((Expr (ATask i p)) (Expr (ATask p o)) (Expr i) -> (Expr o)) | TC i & TC p & iTask i & iTask o & iTask p
runTasksSequence = (RunTasksSequence bm) 
(>>=.) infixl 9 :: (Expr (ATask i p)) (Expr (ATask p o)) -> (Expr i) -> (Expr o) | TC i & TC p & iTask i & iTask o & iTask p
(>>=.) a b = (runTasksSequence a b)

runTasksSeqRedirect :: ((Expr (ATask i z)) (Expr (ATask p o)) (Expr i) (Expr y) (Expr (ATask (z, y) p)) -> (Expr o)) | TC i & TC z & TC y & TC p & iTask i & iTask o & iTask z & iTask p & iTask y
runTasksSeqRedirect = (RunTasksSeqRedirect bm)
(>>|.) infixl 9:: (Expr (ATask i z)) (Expr (ATask p o)) -> (Expr i, Expr y, (Expr (ATask (z, y) p))) -> (Expr o) | TC i & TC z & TC y & TC p & iTask i & iTask o & iTask z & iTask p & iTask y
(>>|.) a b = \(i1, i2, f) . runTasksSeqRedirect a b i1 i2 f
// compWaitLeft = CompWaitLeft bm
// compWaitRight a b = compWaitLeft b a
// compWaitAny	 = CompWaitAny bm
// compWaitBoth = CompWaitBoth bm

waitForButton :: ((Expr Int) (Expr Bool) -> (Expr Void))
waitForButton = (WaitForButton bm)

getButtonPressedBlocking :: (Expr Int)
getButtonPressedBlocking = (GetButtonPressedBlocking bm)


extractReturnedValue :: (ReturnedValue (Expr a)) -> (Expr a)
extractReturnedValue (ReturnedValue v) = v


class If a
where
	If :: (Expr Bool) a a -> a
instance If (Expr a) | iTask a
where
	If cond ba bb = IfExpr bm cond ba bb
instance If (ReturnedValue (Expr a)) | iTask a
where
	If cond ba bb = ReturnedValue (IfRetV bm cond ba bb)


instance == (Expr a) 
where
	== (Task _ aName aParams aBody) (Task _ bName bParams bBody) = (aName == bName) && (paramsNamesEqual aParams bParams)
	where
		paramsNamesEqual [h1:t1] [h2:t2] = if (h1==h2) (paramsNamesEqual t1 t2) False
		paramsNamesEqual [] []		= True
		paramsNamesEqual [] [_:_]	= False
		paramsNamesEqual [_:_] []	= False
	== (Integer _ v1) 		(Integer _ v2)		= v1==v2
	== (Boolean _ v1) 		(Boolean _ v2)		= v1==v2
	== (Str _ v1) 			(Str _ v2) 			= v1==v2
	== (Float _ v1) 		(Float _ v2) 		= v1==v2
	// == (EmptyList _)		(EmptyList _)		= True
	== _ _ = False

buttonLeft ::		 (Expr Int)
buttonLeft		= integer 1
buttonRight ::		 (Expr Int)
buttonRight		= integer 2
buttonUp ::			 (Expr Int)
buttonUp		= integer 3
buttonDown ::		 (Expr Int)
buttonDown		= integer 4
buttonSelect ::		 (Expr Int)
buttonSelect	= integer 5
buttonReset ::		 (Expr Int)
buttonReset		= integer 6

forgetLeftResult :: Expr (ATask (a, b) b) | TC a & TC b & iTask a & iTask b
forgetLeftResult = task "forgetLeftResult" [AtInt "_", AtInt "c"] :=. (variable "c")