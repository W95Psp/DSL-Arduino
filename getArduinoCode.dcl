definition module getArduinoCode

import Expr

:: Result a = Result a | Fail String
getArduinoCode :: (Expr a) -> Result String