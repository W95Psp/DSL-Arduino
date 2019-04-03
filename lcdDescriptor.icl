implementation module lcdDescriptor


import StdString
import iTasks._Framework.Generic

:: LcdDescriptor 		= {
	  ldLine1	:: String
	, ldLine2	:: String
	, ldEvent	:: Int
	}

derive class iTask LcdDescriptor