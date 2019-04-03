definition module Expr


import StdClass
import StdString
import iTasks._Framework.Generic

:: ATaskInputType = AtInt String | AtFloat String | AtBoolean String | AtString String | AtList ATaskInputType
:: BM a b = { t :: a -> b, f :: b -> a }
bm :: BM a a

aTaskInputTypeToStringSquare :: ATaskInputType -> (String, String)


// compose task A et B :: task "compose" (inputA, inputB) 

:: ATask tIn tOut = ATask tOut

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
	| E.b c: 		GetFstTuple2 (BM a b)	(Expr (b, c)) 			& TC b & TC c & iTask c & iTask b
	| E.b c: 		GetSndTuple2 (BM a c)	(Expr (b, c)) 			& TC b & TC c & iTask c & iTask b
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


integer 		:: (Int -> (Expr Int))
boolean 		:: (Bool -> (Expr Bool))
str 			:: (String -> (Expr String))
float 			:: (Real -> (Expr Real))
(*.) 	infixl 7:: ((Expr b) (Expr b) -> (Expr b)) | * b & iTask b
(/.) 	infixl 7:: ((Expr b) (Expr b) -> (Expr b)) | / b & iTask b
(+.) 	infixl 6:: ((Expr b) (Expr b) -> (Expr b)) | + b & iTask b
(-.) 	infixl 6:: ((Expr b) (Expr b) -> (Expr b)) | - b & iTask b
(&&.)	infixl 3:: ((Expr Bool) (Expr Bool) -> (Expr Bool))
(||.)	infixl 3:: ((Expr Bool) (Expr Bool) -> (Expr Bool))
(<.)	infixl 4:: ((Expr b) (Expr b) -> (Expr Bool)) | Ord b & iTask b
(<=.)	infixl 4:: (Expr b) (Expr b) -> (Expr Bool) | Ord b & Eq b & iTask b
notExpr			:: ((Expr Bool) -> (Expr Bool))
(>=.)	infixl 4:: (Expr b) (Expr b) -> (Expr Bool) | Ord b & Eq b & iTask b
(>.)	infixl 4:: (Expr b) (Expr b) -> (Expr Bool) | Ord b & Eq b & iTask b
(==.)	infixl 4:: ((Expr b) (Expr b) -> (Expr Bool)) | Ord b & Eq b & iTask b
(!=.)	infixl 4:: (Expr b) (Expr b) -> (Expr Bool) | Ord b & Eq b & iTask b
task 			:: (String [ATaskInputType] (ReturnedValue (Expr o)) -> (Expr (ATask i o))) | TC i & iTask i & iTask o
variable 		:: (String -> (Expr a)) | TC a
tuple2 			:: ((Expr b, Expr c) 						 -> (Expr (b,c)))		| TC b & iTask b & TC c & iTask c
tuple3 			:: ((Expr b, Expr c, Expr d) 				 -> (Expr (b,c,d)))		| TC b & iTask b & TC c & iTask c & TC d & iTask d
tuple4 			:: ((Expr b, Expr c, Expr d, Expr e) 		 -> (Expr (b,c,d,e)))	| TC b & iTask b & TC c & iTask c & TC d & iTask d & TC e & iTask e
tuple5 			:: ((Expr b, Expr c, Expr d, Expr e, Expr f) -> (Expr (b,c,d,e,f))) | TC b & iTask b & TC c & iTask c & TC d & iTask d & TC e & iTask e & TC f & iTask f
getTimestamp	:: (Expr Int)
getButtonPressed:: (Expr Int)
runTask 		:: (Expr (ATask i o)) (Expr i) -> (ReturnedValue (Expr o))			| TC i & iTask i & iTask o
(:=.) infixr 9 :: ((ReturnedValue (Expr o)) -> (Expr (ATask i o))) (Expr o) -> (Expr (ATask i o))


runTasksSequence :: ((Expr (ATask i p)) (Expr (ATask p o)) (Expr i) -> (Expr o)) | TC i & TC p & iTask i & iTask o & iTask p
// compWaitLeft = CompWaitLeft bm
// compWaitRight a b = compWaitLeft b a
// compWaitAny	 = CompWaitAny bm
// compWaitBoth = CompWaitBoth bm
print 			:: ((Expr String) (Expr Int) (Expr Int) -> (Expr Void))


waitForButton :: ((Expr Int) (Expr Bool) -> (Expr Void))

stringFrom		:: ((Expr b) -> (Expr String)) | toString b & iTask b


class If a
where
	If :: (Expr Bool) a a -> a
instance If (Expr a) | iTask a
instance If (ReturnedValue (Expr a)) | iTask a


(>>=.) infixl 9:: (Expr (ATask i p)) (Expr (ATask p o)) -> (Expr i) -> (Expr o) | TC i & TC p & iTask i & iTask o & iTask p

runTasksSeqRedirect :: ((Expr (ATask i z)) (Expr (ATask p o)) (Expr i) (Expr y) (Expr (ATask (z,y) p)) -> (Expr o)) | TC i & TC z & TC y & TC p & iTask i & iTask o & iTask z & iTask p & iTask y

(>>|.) infixl 9:: (Expr (ATask i z)) (Expr (ATask p o)) -> (Expr i, Expr y, Expr (ATask (z,y) p)) -> (Expr o) | TC i & TC z & TC y & TC p & iTask i & iTask o & iTask z & iTask p & iTask y


getButtonPressedBlocking :: (Expr Int)

gFst :: ((Expr (b, c)) -> (Expr b))		| TC b & TC c & iTask c & iTask b
gSnd :: ((Expr (b, c)) -> (Expr c)) 		| TC b & TC c & iTask c & iTask b

buttonLeft ::		 (Expr Int)
buttonRight ::		 (Expr Int)
buttonUp ::			 (Expr Int)
buttonDown ::		 (Expr Int)
buttonSelect ::		 (Expr Int)
buttonReset ::		 (Expr Int)

forgetLeftResult :: Expr (ATask (a, b) b) | TC a & TC b & iTask a & iTask b
