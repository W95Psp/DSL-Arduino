implementation module guiArduinoSimulator

import iTasks
import StdEnum
import iTasks.API.Extensions.SVG.SVGlet
import lcdDescriptor

color_black = SVGRGB 20 20 20
color_grey = SVGRGB 120 120 120

color_backScreen = SVGRGB 135 173 52
color_backLetter = SVGRGB 124 158 49
color_borderScreen = SVGRGB 48 48 48

color_green = SVGRGB 31 122 52

wLetter = px 20.0
hLetter = px 30.0
mLetter = px  3.0

mScreenW = px 20.0
mScreenH = px 14.0


buttonSVG :: String Int LcdDescriptor (Shared LcdDescriptor) -> Image LcdDescriptor
buttonSVG title id descriptor sdescriptor =
	overlay [(AtMiddleX,AtBottom)] [] [text font title] (Just button)
	where
		button = collage [
				(px 0.0, px 0.0),
				(px 15.0, px 35.0)
			] [
				rect (px 25.0) (px 25.0) <@< {strokewidth = (px 1.0)} <@< {stroke = color_grey} <@< {fill = if (descriptor.ldEvent==id) color_grey color_black},
				empty (px 1.0) (px 1.0)
			] Nothing
			<@< {onclick = updDesc, local = False}
		font = {
					  fontfamily 	= "Courier"
					, fontysize 	= 10.0
					, fontstretch 	= ""
					, fontstyle 	= ""
					, fontvariant 	= ""
					, fontweight 	= ""
				}
		updDesc _ descriptor = {descriptor & ldEvent = id}

LetterFrame = rect wLetter hLetter <@< {strokewidth = zero} <@< {fill = color_backLetter}

displayLetterFrames = collage
	[((px (toReal x)) * (wLetter + mLetter), (px (toReal y)) * (hLetter + mLetter)) \\ x <- [0..15] , y <- [0..1]]
	[LetterFrame \\ x <- [1..16] , y <- [0..1]]
	Nothing

lcdScreen :: LcdDescriptor (Shared LcdDescriptor) -> Image LcdDescriptor
lcdScreen descriptor sdescriptor = collage [
		(px 0.0, px 0.0),
		(mScreenW, mScreenH),
		(mScreenW, mScreenH						- (px 1.2)),
		(mScreenW, mScreenH + mLetter + hLetter	- (px 1.2))
	] [
		rect ((wLetter + mLetter) * (px 16.0) - mLetter + ((px 2.0) * mScreenW)) ((hLetter + mLetter) * (px 2.0) - mLetter + ((px 2.0) * mScreenH)) <@< {strokewidth = px 8.0} <@< {stroke = color_borderScreen}  <@< {fill = color_backScreen},
		displayLetterFrames,
		text font descriptor.ldLine1,
		text font descriptor.ldLine2
	] Nothing
	where
		font = {
					  fontfamily 	= "Courier"
					, fontysize 	= 38.0
					, fontstretch 	= ""
					, fontstyle 	= ""
					, fontvariant 	= ""
					, fontweight 	= ""
				}

lblButtons = ["Left", "Right", "Up", "Down", "Select", "Reset"]
displayLcd :: LcdDescriptor (Shared LcdDescriptor) -> Image LcdDescriptor
displayLcd descriptor sdescriptor = collage 
	[
		(px 5.0, px 5.0),
		(px 10.0, px 110.0)
	]
	[
		lcdScreen descriptor sdescriptor,
		collage
			[(px (toReal (40 * i)), px 0.0) \\ x <- lblButtons & i <- [1..]]
			[buttonSVG x i descriptor sdescriptor \\ x <- lblButtons & i <- [1..]]
			Nothing 
	] (Just (
			empty (px 440.0) (px 180.0)
		))

imageTask :: (Shared LcdDescriptor) -> Task LcdDescriptor
imageTask descriptor =
	updateSharedInformation (Title "Arduino Simulation")
		[imageUpdate
			id							// server state (share) and view are identical
			(\s v tags -> displayLcd s descriptor)
										// generate image
			(\s v -> v)					// update view when state changes
			(\s v -> s)					// update state when view changes
			(\_ s -> Nothing)			// no conflict handling
			(\o n.n)					// always select the new state
		]
		descriptor