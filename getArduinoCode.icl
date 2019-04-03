implementation module getArduinoCode

import StdDebug
import StdBool
import StdString
import StdList
import StdClass

import Expr

// StrExp contient des variable libres
:: StrExp = {
	  seType :: String
	, seBody :: String
	}
:: StrTask = {
	  stName	:: String
	, stExp		:: StrExp
	, stInput	:: [(String, String)]
	}

instance == (String, String)
where
	== (a1, a2) (b1, b2) = (a1==b1) && (a2==b2)
instance == StrExp
where
	== a b = (a.seType==b.seType) && (a.seBody==b.seBody)

instance == StrTask
where
	== a b = (a.stName==b.stName)

mergeStrTasks :: [StrTask] [StrTask] -> [StrTask]
mergeStrTasks list [] = list
mergeStrTasks list [item:rest] = if (isTaskAlreadyIn item list) (mergeStrTasks list rest) [item:mergeStrTasks list rest]

isTaskAlreadyIn :: StrTask [StrTask] -> Bool
// trace ("\n/search "+++ (toString task) +++" in "+++ (listToString [h:t]) +++"/") 
isTaskAlreadyIn task [h:t] = if (task==h) (True) (isTaskAlreadyIn task t)
isTaskAlreadyIn task [] = False

class mergeTSKState ti
where
	mergeTSKState :: ti (Expr a) (([StrTask], StrExp) StrExp -> ([StrTask], StrExp)) -> ([StrTask], StrExp)
instance mergeTSKState [StrTask]
where
	mergeTSKState tasks expr merger = trace "A" mergeTSKState (tasks, {seType = "empty", seBody = ""}) expr merger
instance mergeTSKState ([StrTask], StrExp)
where
	mergeTSKState (tsks, exp) expr merger = trace "B" mergeTSKStateSub (tsks, exp) (buildTasks expr tsks []) merger
mergeTSKStateSub :: ([StrTask], StrExp) ([StrTask], StrExp) (([StrTask], StrExp) StrExp -> ([StrTask], StrExp)) -> ([StrTask], StrExp)
mergeTSKStateSub (tsksA, expA) (tsksB, expB) merger = trace "C" merger (mergeStrTasks tsksA tsksB, expA) expB

:: MergerLamda :== [StrTask] StrExp -> ([StrTask], StrExp)

instance toString (String, String)
where
	toString (a,b) = a +++ " " +++ b

instance toString StrTask
where
	toString t = "{ST "+++ t.stName +++"}"

listToString t = "[" +++ (sub t) +++ "]"
	where
		sub [h] = (toString h)
		sub [h:t] = (toString h) +++ ", " +++ (sub t) 
		sub [] = ""

merge :: [StrTask] ([StrTask], StrExp) MergerLamda -> ([StrTask], StrExp)
merge l1 (l2,exp) fun = fun (mergeStrTasks l1 l2) exp

(~+) infixr 8 :: a b -> (a, b)
(~+) a b = (a, b)
(~~+) infixr 8 :: (a, (b, c)) d -> (a, (b, c, d))
(~~+) (a, (b, c)) d = (a, (b, c, d))
(~~~+) infixr 8 :: (a, (b, c, d)) e -> (a, (b, c, d, e))
(~~~+) (a, (b, c, d)) e = (a, (b, c, d, e))
(~~~~+) infixr 8 :: (a, (b, c, d, e)) f -> (a, (b, c, d, e, f))
(~~~~+) (a, (b, c, d, e)) f = (a, (b, c, d, e, f))

class ~> a b
where
	(~>) infixl 7:: (([StrTask], [(String,String)]), a) (b,b) -> ([StrTask], StrExp)

instance ~> (Expr a) (String -> String)
where
	(~>) ((tasks, vars), exp) (funBody, funType) = merge tasks (buildTasks exp tasks vars) handle
	where
		handle tasks se = (tasks, {seType = funType se.seType, seBody = funBody se.seBody})

instance ~> (Expr a, Expr b) (String String -> String)
where
	(~>) ((tasks, vars), (exp1, exp2)) (funBody, funType) = merge tasks (buildTasks exp1 tasks vars) (\tasks s1 . 
			merge tasks (buildTasks exp2 tasks vars) (\tasks s2 . 
				handle tasks s1 s2
			)
		)
	where
		handle tasks s1 s2 = (tasks, {seType = funType s1.seType s2.seType, seBody = funBody s1.seBody s2.seBody})

instance ~> (Expr a, Expr b, Expr c) (String String String -> String)
where
	(~>) ((tasks, vars), (exp1, exp2, exp3)) (funBody, funType) = merge tasks (buildTasks exp1 tasks vars) (\tasks s1 . 
			merge tasks (buildTasks exp2 tasks vars) (\tasks s2 . 
				merge tasks (buildTasks exp3 tasks vars) (\tasks s3 . 
					handle tasks s1 s2 s3
				)
			)
		)
	where
		handle tasks s1 s2 s3 = (tasks, {seType = funType s1.seType s2.seType s3.seType, seBody = funBody s1.seBody s2.seBody s3.seBody})

instance ~> (Expr a, Expr b, Expr c, Expr d) (String String String String -> String)
where
	(~>) ((tasks, vars), (e1, e2, e3, e4)) (funBody, funType) = merge tasks (buildTasks e1 tasks vars) (\tasks s1 . 
			merge tasks (buildTasks e2 tasks vars) (\tasks s2 . 
				merge tasks (buildTasks e3 tasks vars) (\tasks s3 . 
					merge tasks (buildTasks e4 tasks vars) (\tasks s4 . 
						handle tasks s1 s2 s3 s4
					)
				)
			)
		)
	where
		handle tasks s1 s2 s3 s4 = (tasks, {seType = funType s1.seType s2.seType s3.seType s4.seType, seBody = funBody s1.seBody s2.seBody s3.seBody s4.seBody})

instance ~> (Expr a, Expr b, Expr c, Expr d, Expr e) (String String String String String -> String)
where
	(~>) ((tasks, vars), (e1, e2, e3, e4, e5)) (funBody, funType) = merge tasks (buildTasks e1 tasks vars) (\tasks s1 . 
			merge tasks (buildTasks e2 tasks vars) (\tasks s2 . 
				merge tasks (buildTasks e3 tasks vars) (\tasks s3 . 
					merge tasks (buildTasks e4 tasks vars) (\tasks s4 . 
						merge tasks (buildTasks e5 tasks vars) (\tasks s5 . 
							handle tasks s1 s2 s3 s4 s5
						)
					)
				)
			)
		)
	where
		handle tasks s1 s2 s3 s4 s5 = (tasks, {seType = funType s1.seType s2.seType s3.seType s4.seType s5.seType, seBody = funBody s1.seBody s2.seBody s3.seBody s4.seBody s5.seBody})


typeAutoResolver :: String String -> String
typeAutoResolver a b = if (a==b) a (indetails a b)
where
	indetails "empty" a = a 
	indetails a "empty" = a 
	indetails _ _ = "?error?" 

isBasicExpr :: (Expr a) -> Bool
isBasicExpr (Integer _ _) = True 
isBasicExpr (Boolean _ _) = True 
isBasicExpr (Str _ _) = True 
isBasicExpr (Float _ _) = True
isBasicExpr (Variable _) = True
isBasicExpr (GetTimestamp _) = True
isBasicExpr _ = False
buildTasks_writeOp :: [StrTask] (Expr a) (Expr b) String [(String, String)] -> ([StrTask], StrExp)
buildTasks_writeOp t ra rb op vars = (t, vars) ~+ ra ~+ rb ~> (\a b. (((write ra) a) +++ op +++ ((write rb) b)), typeAutoResolver)
where
	write s = if (isBasicExpr s) id p
	p s = "(" +++ s +++ ")"
	id a = a

buildParams [h:l] = [aTaskInputTypeToStringSquare h:buildParams l]
buildParams [] = []

concatExpStrs [(type, s)] _ 		= s
concatExpStrs [(type, s):strs] join = s +++ join +++ (concatExpStrs strs join)
concatExpStrs [] _ 					= ""

fromVarTypes :: [(String, String)] String -> (String, Int)
fromVarTypes vars var = sub vars var 0
where
	sub [(type,name):vars] var nth = if (var==name) (type, nth) (sub vars var (nth + 1))
	sub [] var nth = ("undefined", -1)

buildTasks :: (Expr a) [StrTask] [(String, String)] -> ([StrTask], StrExp)
buildTasks (BindTasks _ ta1 tb1) 		tsks _ = (tsks, {seType = "empty", seBody = ""})
// buildTasks (CompWaitLeft _ a b) 		tsks _ = (tsks, {seType = "empty", seBody = ""})
// 		(tsks, vars) ~+ a ~+ b ~> (
// 				\a b . "cb = CreateCallbackContext(\"" +++ a +++ "\", WAIT_FOR_RIGHT, _cTask->cbId);",
// 				\a b . a
// 			)
// 		//	int cb = CreateCallbackContext("B", WAIT_FOR_RIGHT, _cTask->cbId);
// 		// 	CALL("A1", new vector<void*>(), getCbCtxId(cb, 1));
// 		// 	CALL("A2", new vector<void*>(), getCbCtxId(cb, 0));
// buildTasks (CompWaitAny  _ a b) 		tsks _ = (tsks, {seType = "empty", seBody = ""})
// buildTasks (CompWaitBoth _ a b) 		tsks _ = (tsks, {seType = "empty", seBody = ""})
buildTasks (Task _ aName aParams (ReturnedValue aBody)) 		tsks _ = if (isTaskAlreadyIn task tsks) (tsks, emptyExp) itIsANewTask
where
	itIsANewTask = (remplace newTasks {task & stExp = strExp}, {seType = "empty", seBody = aName})
	remplace [t:tasks] tt = if (t==tt) [tt:tasks] [t:remplace tasks tt]
	remplace [] tt = []
	(newTasks, strExp) = buildTasks aBody (mergeStrTasks tsks [task]) task.stInput
	task = {
		  stName	= aName
		, stExp		= emptyExp
		, stInput	= buildParams aParams
		}
	emptyExp = {seType = "empty", seBody = ""}

buildTasks (Integer _ v) 						tsks _ = (tsks, {seType = "int", seBody = toString v})
buildTasks (GetTimestamp _) 					tsks _ = (tsks, {seType = "int", seBody = "((int) time(NULL))"})
buildTasks (GetButtonPressed _) 				tsks _ = (tsks, {seType = "int", seBody = "key"})
buildTasks (Boolean _ v) 						tsks _ = (tsks, {seType = "int", seBody = if v "1" "0"})
buildTasks (Str _ v) 							tsks _ = (tsks, {seType = "string", seBody = "\"" +++ v +++ "\""})
buildTasks (Float _ v) 							tsks _ = (tsks, {seType = "float", seBody = toString v})
// buildTasks (EmptyList _) 						tsks _ = (tsks, {seType = "int", seBody = "CreateEmptyList()"})
// buildTasks (AddList _ v l) 						tsks = tsks ~+ v ~+ l ~> \v l . "PushIntoList(" +++ v +++ ", " +++ l +++ ")"
// buildTasks (Length _ x) 						tsks = (tsks, "exp")
buildTasks (Mul _ a b) 						tsks vars = buildTasks_writeOp tsks a b "*" vars
buildTasks (Div _ a b) 						tsks vars = buildTasks_writeOp tsks a b "/" vars
buildTasks (Plus _ a b) 					tsks vars = buildTasks_writeOp tsks a b "+" vars
buildTasks (Minus _ a b) 					tsks vars = buildTasks_writeOp tsks a b "-" vars
buildTasks (Le _ a b) 						tsks vars = buildTasks_writeOp tsks a b " < " vars
buildTasks (Eq _ a b) 						tsks vars = buildTasks_writeOp tsks a b " == " vars
buildTasks (Not _ a) 						tsks vars = (tsks, vars) ~+ a ~> (\a . "!(" +++ a +++ ")", \a . a)
buildTasks (And _ a b) 						tsks vars = buildTasks_writeOp tsks a b " && " vars
buildTasks (Or _ a b) 						tsks vars = buildTasks_writeOp tsks a b " || " vars
// buildTasks (ComposeExpr _ (ReturnedValue a) (ReturnedValue b)) tsks vars = 
// 		(tsks, vars) ~+ a ~+ b ~> (
// 			\a b . "composeRight(" +++ a +++ ", " +++ b +++ ")",
// 			\a b . b
// 		)
// buildTasks (RunTask _ t p)	 					tsks = (tsks, {seType = "empty", seBody = ""})
// buildTasks (RunTask _ t p)	 					tsks = tsks ~+ t ~+ p ~> (\t p . "CALL(" +++ t +++ ", " +++ p +++ ")", \_ _. "void")
buildTasks (RunTask _ t p)	 				tsks vars = (tsks, vars) ~+ t ~+ p ~> (
			\t p . "CALL(\"" +++ tStr t +++ "\", makeVoidVector" +++ (get p) +++ ", _cTask->cbId);", \_ _. "call-task"
		)
	where
		get pstr = if False pstr ("(" +++ pstr +++ ")")
		isTuple = case p of
			(Tuple2 _ _) = True
			(Tuple3 _ _) = True
			(Tuple4 _ _) = True
			(Tuple5 _ _) = True
			_			 = False
		tStr :: String -> String
		tStr _ = case t of
			(Task _ aName aParams aBody) = aName
buildTasks (Tuple2 _ (a,b))		 			tsks vars = (tsks, vars) ~+ a ~+ b ~> (\a b. a +++ "," +++ b, \a b. "tuple_")
buildTasks (Tuple3 _ (a,b,c))	 			tsks vars = ((tsks, vars) ~+ a ~+ b) ~~+ c ~> (\a b c. a +++ ", " +++ b +++ ", " +++ c, \_ _ _ . "tuple")
// buildTasks (Tuple4 _ (a,b,c,d))				tsks _ = (tsks, {seType = "tuple", seBody = concatExpStrs a b c d})
// buildTasks (Tuple5 _ (a,b,c,d,e))			tsks _ = (tsks, {seType = "tuple", seBody = concatExpStrs [a, b, c, d, e]})
// buildTasks (Variable v)		 					tsks vars = trace (listToString vars) (tsks, {seType = "resolve-var", seBody = v})
buildTasks (Variable vname)	 				tsks vars = (tsks, {seType = typev, seBody = body})
where
	body = "getArg_" +++ typev +++ "(params[" +++ (toString nth) +++ "])"
	(typev, nth) = fromVarTypes vars vname
buildTasks (IfExpr _ cond a b)	 			tsks vars = (ntasks, nexp)
where
	(ntasks, nexp) = ((tsks, vars) ~+ cond ~+ a) ~~+ b ~> (\cond a b . "(" +++ cond +++ ") ? (" +++ a +++ ") : (" +++ b +++ ")", \_ a _ . a)
buildTasks (IfRetV _ cond aR bR) 			tsks vars = (ntasks, nexp)
where
	(ntasks, nexp) = ((tsks, vars) ~+ cond ~+ a) ~~+ b ~> (\cond a b . "if (" +++ cond +++ "){" +++ (cnvEA a) +++ "} else {"+++ (cnvEB b) +++"}", \_ _ _ . "ready")
	cnvEA body = renderExpression aType body
	cnvEB body = renderExpression bType body
	aType = case buildTasks a tsks vars of (_, x) = x.seType
	bType = case buildTasks b tsks vars of (_, x) = x.seType
	(a, b) = (case aR of ReturnedValue v = v, case bR of ReturnedValue v = v)
// | E.i o z:	RunTasksKeepLeft (BM a o) 		(Expr (ATask i o)) (Expr (ATask i z)) (Expr i)			& TC i & iTask i & iTask o & iTask z
// | E.i o p:	RunTasksKeepBoth (BM a (o,p)) 	(Expr (ATask i o)) (Expr (ATask i p)) (Expr i)			& TC i & iTask i & iTask o & iTask p
// | E.i o:	RunTasksKeepAny  (BM a o) 		(Expr (ATask i o)) (Expr (ATask i o)) (Expr i)			& TC i & iTask i & iTask o
// | E.i o p:	RunTasksSequence (BM a o) 		(Expr (ATask i p)) (Expr (ATask p o)) (Expr i)			& TC i & iTask i & iTask o & iTask p

buildTasks (RunTasksKeepLeft _ a b i)			tsks vars = ((tsks, vars) ~+ a ~+ b) ~~+ i ~> (
			\a b i. 
				"cb = CreateCallbackContext(\""+++"\", WAIT_FOR_LEFT, _cTask->cbId);\n " +++ 
				"CALL(\"" +++ a +++ "\", makeVoidVector" +++ (get i) +++ ", getCbCtxId(cb, 0));\n " +++
				"CALL(\"" +++ b +++ "\", makeVoidVector" +++ (get i) +++ ", getCbCtxId(cb, 1));\n"
			, \_ _ _. "call-task"
		)
	where
		get pstr = if False pstr ("(" +++ pstr +++ ")")
buildTasks (RunTasksKeepBoth _ a b i)			tsks vars = ((tsks, vars) ~+ a ~+ b) ~~+ i ~> (
			\a b i. 
				"cb = CreateCallbackContext(\""+++"\", WAIT_FOR_BOTH, _cTask->cbId);\n" +++ 
				"CALL(\"" +++ a +++ "\", makeVoidVector" +++ (get i) +++ ", getCbCtxId(cb, 0));" +++
				"CALL(\"" +++ b +++ "\", makeVoidVector" +++ (get i) +++ ", getCbCtxId(cb, 1));"
			, \_ _ _. "call-task"
		)
	where
		get pstr = if False pstr ("(" +++ pstr +++ ")")
buildTasks (RunTasksKeepAny _ a b i)			tsks vars = ((tsks, vars) ~+ a ~+ b) ~~+ i ~> (
			\a b i. 
				"cb = CreateCallbackContext(\""+++"\", WAIT_FOR_ANY, _cTask->cbId);\n " +++ 
				"CALL(\"" +++ a +++ "\", makeVoidVector" +++ (get i) +++ ", getCbCtxId(cb, 0));\n" +++
				"CALL(\"" +++ b +++ "\", makeVoidVector" +++ (get i) +++ ", getCbCtxId(cb, 1));\n"
			, \_ _ _. "call-task"
		)
	where
		get pstr = if False pstr ("(" +++ pstr +++ ")")

buildTasks (ConcatSTR _ a b)			tsks vars = (tsks, vars) ~+ a ~+ b ~> (
			\a b. 
				"(" +++ a +++ " + "+++ b +++ ")"
			, \x _. x
		)
	where
		get pstr = if False pstr ("(" +++ pstr +++ ")")
buildTasks (ToString _ a)			tsks vars = (tsks, vars) ~+ a ~> (
			\a. 
				"to_string(" +++ a +++ ")"
			, \x.x
		)
	where
		get pstr = if False pstr ("(" +++ pstr +++ ")")
buildTasks (VoidExpr _)			tsks vars = trace "\nWarning: use of not supported function (VoidExpr) \n" (tsks, {seBody = "getVoid()", seType = ""})
buildTasks (GetFstTuple2 _ a)	tsks vars = trace "\nWarning: use of not supported function (GetFstTuple2) \n" (tsks, {seBody = "notSupportedYet()", seType = ""})
buildTasks (GetSndTuple2 _ a)	tsks vars = trace "\nWarning: use of not supported function (GetSndTuple2) \n" (tsks, {seBody = "notSupportedYet()", seType = ""})

// buildTasks (RunTasksSequence _ a b i) 		tsks _ = if (isTaskAlreadyIn task tsks) (tsks, emptyExp) newTasks
// where
// 	strExp = 
// 	(newTasks, _) = (tsks, vars)  ~+ a ~+ b ~> (\a b . a +++ b, \a b . a +++ b)
// 	// (newTasks, strExp) = buildTasks aBody (mergeStrTasks tsks [task]) task.stInput
// 	task = {
// 		  stName	= aName +++ " >>= " +++ bName 
// 		, stExp		= emptyExp
// 		, stInput	= buildParams (concat aParams bParams)
// 		}
// 	emptyExp = {seType = "empty", seBody = ""}
// 	aName = case a of (Task _ n _ _) = n
// 	aParams = case a of (Task _ _ n _) = n
// 	bName = case b of (Task _ n _ _) = n
// 	bParams = case b of (Task _ _ n _) = n

buildTasks (RunTasksSequence _ a b i)			tsks vars = ((tsks, vars) ~+ a ~+ b) ~~+ i ~> (
			\a b i. 
				"cb = CreateCallbackContext(\"" +++ (bStr b) +++ "\", CALL_A_TASK, _cTask->cbId);\n" +++ 
				"CALL(\"" +++ (aStr a) +++ "\", makeVoidVector" +++ (get i) +++ ", getCbCtxId(cb, 0));\n"
			, \_ _ _. "call-task"
		)
	where
		get pstr = if False pstr ("(" +++ pstr +++ ")")

		aStr :: String -> String
		aStr v = getTaskName a
		bStr :: String -> String
		bStr v = getTaskName b
buildTasks (RunTasksSeqRedirect _ a b iA iB c)	tsks vars = ((((tsks, vars) ~+ a ~+ b) ~~+ iA) ~~~+ iB) ~~~~+ c ~> (
			\a b iA iB c.
				"//This wont work, some work left here "+++c+++" \ncb = CreateCallbackContext(\"" +++ (bStr b) +++ "\", CALL_A_TASK_SHIFT_DATA, _cTask->cbId);\n" +++
				"cb->someData = makeVoidVector(" +++ iB +++ ");\n" +++ 
				"CALL(\"" +++ (aStr a) +++ "\", makeVoidVector" +++ (get iA) +++ ", getCbCtxId(cb, 0));\n"
			, \_ _ _ _ _. "call-task"
		)
	where
		get pstr = if False pstr ("(" +++ pstr +++ ")")

		aStr :: String -> String
		aStr v = getTaskName a
		cStr :: String -> String
		cStr v = getTaskName c
		bStr :: String -> String
		bStr v = getTaskName b
buildTasks (Print _ str px py)			tsks vars = ((tsks, vars) ~+ px ~+ py) ~~+ str ~> (
		\x y s . "printArduino(" +++ s +++ ", " +++ x +++ ", " +++ y +++ ")",
		\x y s . "nothing interesting"
	)
buildTasks (GetButtonPressedBlocking _ )				tsks vars = buildTasks V tsks vars
where
	V = case runTask RoutineWaitForAnyButton (VoidExpr bm) of (ReturnedValue v) = v
buildTasks (WaitForButton _ codeButton state)			tsks vars = buildTasks V tsks vars
where
	V = case runTask RoutineWaitForButton (tuple2 (codeButton, state)) of (ReturnedValue v) = v

buildTasks _				 					tsks _ = trace "?Error?" (tsks, {seType = "empty", seBody = ""})


RoutineWaitForButton :: Expr (ATask (Int, Bool) Int)
RoutineWaitForButton = task "RoutineWaitForButton" [AtInt "b", AtBoolean "state"] (
		If (getButtonPressed ==. (variable "b"))
			(ReturnedValue (integer 0))
			(runTask RoutineWaitForButton (tuple2 (variable "b", variable "state")))
	)

RoutineWaitForAnyButton :: Expr (ATask Void Int)
RoutineWaitForAnyButton = task "RoutineWaitForAnyButton" [AtInt "b"] (
		If (getButtonPressed ==. (integer 0))
			(runTask RoutineWaitForAnyButton (VoidExpr bm))
			(ReturnedValue getButtonPressed)
	)


// taskA :: Expr (ATask (Int, Int) Int)
// taskA = task "taskA" [AtInt "a", AtInt "b"] (
// 		If ((variable "b") <. (integer 200)) (
// 				runTask taskA (tuple2 (mul (getTimestamp) (integer 2), mul (variable "b") (integer 2)))
// 			) (
// 				runTask wait (integer 8000)
// 			)
// 	)

getTaskName (Task _ n _ _) = n
isTuple (Tuple2 _ _) = True
isTuple (Tuple3 _ _) = True
isTuple (Tuple4 _ _) = True
isTuple (Tuple5 _ _) = True
isTuple _ 			 = False
// oo :: Expr (ATask (Int, Int) Int)
// oo2 = runTask oo1 ss
// where
// 	ss :: Expr Int
// 	ss = integer 2

// a = Task (Choses)

// CALL a -> vérifie si la tâche existe, si c'est le cas on redirige

// ce qu'on veut :  epxressions -> (tableau de strings du genre rawStr, var name, rawstr, var name...) + (avec indication de type)
// 					tasks -> une expression (type=type de retour), type d'entrée + noms d'entrée + un ID !

// auqnd on extrait une expr, on a une expression et éventuellement un appel à une procédure

// renderCallbackTrigger body = if (exp.seType=="call-task" || exp.seType=="ready") (
// 						exp.seBody +++ "\n"
// 					) (renderCallbackTrigger exp.seBody)

renderExpression type body = if (type=="call-task" || type=="ready") (
						body +++ "\n"
					) ("triggerCallbackContextData = makeVoidVector(" +++ body +++ "); \n triggerCallbackContextIdent = _cTask->cbId; \n")


:: Result a = Result a | Fail String

getArduinoCode :: (Expr a) -> Result String
getArduinoCode main = if (strExp.seType=="empty") (Result allStr) (Fail "Give task first")
where
	allStr = "\n\n" +++ (sub allListStr) +++ " { cout << \"TASK \" << _ << \" NOT FOUND! QUIT\" << endl; exit(1); } \n\n"
	where
		sub [h:l] = h +++ (sub l)
		sub [] = ""
	allListStr = map strTaskToString strTasks
	strTaskToString task = 	"if(_==\"" +++ task.stName +++ "\"){\n"
						+++ (strExpToString task.stExp)
						+++ "} else "
	strExpToString exp = "\t" +++ renderExpression exp.seType exp.seBody;
	(strTasks, strExp) = buildTasks main [] [] 

// Start = getArduinoCode bb1

// Start = buildTasks (Minus bm (integer 2) ((Mul bm (integer 20) (integer 40)))) []
// Start = buildTasks taskExample []