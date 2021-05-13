import pdfminer
from pdfminer.layout import LAParams
from pdfminer.pdfinterp import PDFResourceManager
from pdfminer.converter import PDFPageAggregator
from pdfminer.pdfpage import PDFPage
from pdfminer.layout import LTTextBoxHorizontal
from pdfminer.pdfinterp import PDFPageInterpreter
from pdfminer.pdfdocument import PDFDocument
from pdfminer.pdfparser import PDFParser
from pdfminer.layout import LTChar, LTComponent, LTTextContainer, LTText
from pdfminer.pdftypes import dict_value, PDFObjRef
import pdfrw

import re
import sys
import collections
from weakref import proxy
import time
import subprocess
import json
from urllib import error as urlerror
import argparse
import math
from datetime import datetime
import requests
import urllib.parse
from collections import OrderedDict

import cv2
import numpy as np
import matplotlib.pyplot as plt

from unidecode import unidecode # $ pip install Unidecode
import tzlocal  # $ pip install tzlocal


from astroquery import nasa_ads as na
# if you don't store your token as an environment variable
# or in a file, give it here
adsToken = ''

if adsToken == '':
	try:
		with open("ads_token.txt",'r') as fp:
			for line in fp:
				adsToken = line.strip()
		print("Found Token with file : ",adsToken)
	except:
		pass
else:
	if adsToken != "":
		print("Using token in script : ",adsToken)

if adsToken != "":
	na.ADS.TOKEN = adsToken
else:
	print("Warning! ADS Token is empty, ensure using an enviromental variable or create the 'ads_token.txt' file and place in there")
	ans = input("Would you like to quit [y/n] >")
	if ans == "y":
		sys.exit(0)
	else:
		pass
# by default, the top 10 records are returned, sorted in
# reverse chronological order. This can be changed

# change the fields that are returned (enter as strings in a list)
# We only need the title and bibcode
na.ADS.ADS_FIELDS = ['title', 'bibcode']

#How many more queries can we make today?
getStarRes = na.ADS.query_simple("star",get_raw_response=True,cache=False)
starHeadDict = getStarRes.headers

resetTimestamp = float(starHeadDict["X-RateLimit-Reset"])
local_timezone = tzlocal.get_localzone() # get pytz timezone
resetLocalTime = datetime.fromtimestamp(resetTimestamp, local_timezone)
print("========================")
print("ADS Rate Limit Info")
print("Current Query Limit : ",starHeadDict["X-RateLimit-Limit"])
print("Query Amount Remaining : ",starHeadDict["X-RateLimit-Remaining"])
print("Will reset at ",resetLocalTime.strftime("%Y-%m-%d %H:%M %p (%Z)"))
print("========================")

linksDict = {}
pageObjIds = []
pageIds = []

#Turn the pdf tree into something manipulatable by python
class destTreeNode:
	def __init__(self,curD):
		if type(curD) == PDFObjRef:
			curD = curD.resolve()
		self.selfRep = curD
		self.kids = []
		if type(curD) == dict:
			if "Kids" in curD.keys():
				for uK in curD["Kids"]:
					cK = destTreeNode(uK)
					self.kids.append(cK)

#We will need to break up the page into columns
#Before breaking it up into paragraphs
class textColumn:
	def __init__(self,firstElem,thres=10.0):
		self.minX = firstElem[1][0]
		self.minY = firstElem[1][1]
		self.maxX = firstElem[1][2]
		self.maxY = firstElem[1][3]
		self.threshold = thres
		self.children = [firstElem]
		self.flag = 0

	def inCol(self,testEle):
		threshY = self.getLineHeight()
		if (testEle[1][1] <= (self.maxY + threshY)) and ((self.minY - threshY) <= testEle[1][3]) and (testEle[1][0] <= (self.maxX + self.threshold)) and ((self.minX - self.threshold) <= testEle[1][2]):
			return True
		return False

	def addChild(self,testEle):
		if testEle[1][0] < self.minX:
			self.minX = testEle[1][0]
		if testEle[1][1] < self.minY:
			self.minY = testEle[1][1]
		if testEle[1][2] > self.maxX:
			self.maxX = testEle[1][2]
		if testEle[1][3] > self.maxY:
			self.maxY = testEle[1][3]
		self.children.append(testEle)
		self.flag = 0

	def organizeChildren(self, forceRebuild=False):
		if (self.flag == 0) or forceRebuild:
			copyChil = self.children.copy()
			self.children = sorted(copyChil, key=lambda x: x[1][1], reverse=True)
			self.flag = 1

	def getChildren(self):
		self.organizeChildren()
		return self.children

	def getLineHeight(self,eps=1.15):
		if len(self.children) == 0:
			return 0
		lineHeights = []
		for child in self.children:
			lineHeights.append(abs(child[1][3] - child[1][1]))
		avgHeight = sum(lineHeights)/len(lineHeights)
		return avgHeight * eps

	def _buildLine(self, curLine):
		nBoxes = len(curLine) - 1
		newBBox = [99999,99999,-99999,-99999]
		newLineStr = ""
		copyLine = curLine.copy()
		curLine = sorted(copyLine, key=lambda x: x[1][0])
		for boxI, box in enumerate(curLine):
			addSpace = ""
			if boxI != nBoxes:
				addSpace = " "
			newLineStr += box[0] + addSpace
			curBBox = box[1]
			#x0
			if curBBox[0] < newBBox[0]:
				newBBox[0] = curBBox[0]
			#y0
			if curBBox[1] < newBBox[1]:
				newBBox[1] = curBBox[1]
			#x1
			if curBBox[2] > newBBox[2]:
				newBBox[2] = curBBox[2]
			#y1
			if curBBox[3] > newBBox[3]:
				newBBox[3] = curBBox[3]
		return (newLineStr,newBBox)

	def checkForBadLines(self):
		childWithYs = {}
		for child in self.children:
			curChildY0 = math.floor(child[1][1])
			if curChildY0 in childWithYs.keys():
				#we are on a already examined line
				childWithYs[curChildY0].append(child)
			else:
				#we are on a different line
				childWithYs[curChildY0] = [child]
		newChildList = []
		for childArr in childWithYs.values():
			stitchedLine = self._buildLine(childArr)
			newChildList.append(stitchedLine)
		self.children = newChildList.copy()
		self.organizeChildren(True)

#The mega object which needs to
#store data about itself due to the number of
#steps needed between extracting the inline citations
#connecting them to a citation on the citation page
#parsing the citation, then searching ADS for
#that citation; then finally replacing the
#GOTO inline links with an ADS link
class linkDocObj:
	def __init__(self, annoObj, uri, pos, pageid):
		self.origObjs = [annoObj]
		self.gotoLoc = uri
		self.assocText = [""]
		self.assocTextIn = 0
		self.positions = [[LTComponent(pos),pageid]]
		self.destPage = None
		self.unparseCite = ""
		self.finalCiteStr = ""
		self.papObj = None
		self.papLink = ""
		self.author = ""
		self.year = ""

	def addObj(self,obj):
		self.origObjs.append(obj)

	def addPosition(self, pos, pageid):
		self.positions.append([LTComponent(pos),pageid])

	def linkContains(self, element, pageid):
		if not type(element) is LTChar:
			return False
		for testPos in self.positions:
			if pageid != testPos[1]:
				continue
			if testPos[0].is_hoverlap(element) and testPos[0].is_voverlap(element) :
				return True
		return False

	def addAssocText(self,text):
		self.assocText[self.assocTextIn] += unidecode(text)

	def increaseText(self):
		self.assocText.append("")
		self.assocTextIn += 1

	def getAllText(self):
		self.assocText = [x.replace("- ","") for x in self.assocText]
		retText = [x for x in self.assocText if x != ""]
		return retText

	def getURI(self):
		return self.gotoLoc

	def setDestPage(self,pageNum):
		self.destPage = pageNum

	def getDestPage(self):
		return self.destPage

	def setCiteStr(self,stt):
		self.finalCiteStr = stt

	def setPaperObj(self,papObj_):
		self.papObj = papObj_

	def setPaperLink(self,link_):
		self.papLink = link_

	def getPaperLink(self):
		return self.papLink

	def __str__(self):
		retStr = ""
		for obss in self.origObjs:
			retStr += f"{obss.resolve()} ;"
		return retStr

#Arbitrary element selector for a command-line interface
def arraySelector(array, question,itemPrint = lambda x: x,itemOutput= lambda x:x,autoSelect = lambda x: False):
	for item in array:
		if autoSelect(item):
			return item
	while True:
		print(question)
		for i,v in enumerate(array):
			itemName = itemPrint(v)
			print(i+1,") ",itemName)
		num = input("[1 - "+str(len(array))+"] >  ")
		if num == 'q':
			sys.exit(0)
		try:
			num = int(num)
			if 0 < num and num <= len(array):
				num -= 1
				itemReturn = itemOutput(array[num])
				return itemReturn
			else:
				print("Please input a number between 1 and ",len(array))
		except ValueError:
			print("That's not an number!")

#parses a LTTextBoxHorizontal into a list of lines of text
def getText(element):
	retLines = []
	curLine = ""
	for line in element._objs:
		lineX0 = min(line.x0,line.x1)
		lineX1 = max(line.x0,line.x1)
		lineY0 = min(line.y0,line.y1)
		lineY1 = max(line.y0,line.y1)
		lastX = lineX0
		charWidth = 0
		charsum = 0
		charnum = 0
		charWidthBounds = 999
		for char in line._objs:
			if type(char) == LTChar:
				charX0 = min(char.x0,char.x1)
				charX1 = max(char.x0,char.x1)
				charY0 = min(char.y0,char.y1)
				charY1 = max(char.y0,char.y1)
				#If the parser broke and accidentally put two lines together which shouldn't be together
				if ((charX1 - lastX) > charWidthBounds):
					retLines.append([unidecode(curLine),[lineX0,lineY0,charX1,lineY1], charsum/charnum])
					charsum = 0
					charnum = 0
					lineX0 = charX1
					curLine = ""
				lastX = charX1
				charWidth = abs(charX1 - charX0)
				charWidthBounds = charWidth * 5.5
				charsum += charWidth
				charnum +=  1
				curLine += char.get_text()
			else:
				curLine += " "
		retLines.append([unidecode(curLine), [lineX0,lineY0,lineX1,lineY1], charsum/charnum])
		curLine = ""
	return retLines

def stitchString(stringArr):
	retStr = ""
	for stringPart in stringArr:
		for ss in stringPart.split():
			revRetS = retStr[::-1].strip()
			revSS = ss[::-1].strip()
			if revRetS.find(revSS) > 0:
				retStr = "".join(retStr.rsplit(ss,1)[0],ss) + " "
			else:
				retStr +=  " " + ss
	return retStr


def addToDict(dict,key,value):
	if key in dict.keys():
		dict[key].append(value)
	else:
		dict[key] = [value]

#The "page" object has a pageid, which
#we can use to figure out the page number (after processing the document)
def getPageNumWithPageObj(pageObj):
	global pageObjIds
	return (pageObjIds.index(pageObj.pageid) + 1)

#goto links don't reference the "page" object of thier target location,
#instead refernce the pdfstream object of thier target location; so
#use that instead after building the document tree
def getPageNumber(pageCont):
	global pageIds
	return (pageIds.index(pageCont.objid) + 1)

#build the page order of pdfstream objects inside a goto link
def analyzeKids(curNode):
	global pageIds
	if len(curNode.kids) > 0:
		for kid in curNode.kids:
			analyzeKids(kid)
	else:
		selfRepCon = curNode.selfRep["Contents"]
		if type(selfRepCon) == PDFObjRef:
			pageIds.append(selfRepCon.objid)
		elif type(selfRepCon) == list:
			pageIds.append(selfRepCon[0].objid)
		else:
			print("ERROR! Unknown type for document tree construction")
			print(selfRepCon)
			sys.exit(0)

#Helper with author extraction
def isNone(test):
	if test is None:
		return 0
	else:
		return 1

#get the leaves of a tree no matter how deep
def getbottomNodes(treeNode,botNodes):
	if len(treeNode.kids) > 0:
		for kid in treeNode.kids:
			getbottomNodes(kid,botNodes)
	else:
		botNodes.append(treeNode)


#Directly search ADS without using query_simple
def ads_search(searchQ):
	searchqp = urllib.parse.quote_plus(searchQ)
	request_fields = na.ADS._fields_to_url()
	request_sort = na.ADS._sort_to_url()
	request_rows = na.ADS._rows_to_url(na.ADS.NROWS, na.ADS.NSTART)
	requestURL = na.ADS.QUERY_SIMPLE_URL + "q=" + searchqp + request_fields + request_sort + request_rows
	response = na.ADS._request(method='GET', url=requestURL, headers={'Authorization': 'Bearer ' + na.ADS._get_token()}, timeout=na.ADS.TIMEOUT)
	return response


# We want to narrow it down as much as possible; so try multiple queries if fail or more than 1
def attempt_ads(adsParts):
	attempts = [["author","year"],["author","year","volume"],["author","year","page"],["author","year","volume","page"],["page","year","volume","bibstem"]]
	workingPapers = [[""]]*100
	trueAdsSearchString = ""
	for attempt in attempts:
		try:
			time.sleep(3)
			attAdsParts = {}
			for attK, attV in adsParts.items():
				if attK in attempt:
					attAdsParts[attK] = attV
			adsSearchStringtemp = "".join(list(attAdsParts.values())).strip()
			if adsSearchStringtemp == "":
				continue
			papers = na.ADS.query_simple(adsSearchStringtemp)
			if len(papers) < len(workingPapers):
				print("Results returned!")
				workingPapers = papers.copy()
				trueAdsSearchString = adsSearchStringtemp
		except Exception as e:
			print(e)
			continue
	if len(workingPapers) < 99:
		return (workingPapers,trueAdsSearchString)
	return (None,"".join(list(adsParts.values())).strip())

def findNextClosest(array, targetVal):
	array.sort()
	for item in array:
		if item > targetVal:
			return item
	return 0

def findClosest(array, targetVal):
	return min([(tV,abs(tV - targetVal)) for tV in array],key=lambda x: x[1])[0]



parser = argparse.ArgumentParser(
	description='This program replaces the citation links inside a pdf which just goes to the page with the ADS abstract link'
)
parser.add_argument('input', help='The input pdf file')
parser.add_argument('output', help='The processed output pdf file')

args = parser.parse_args()

inputPDFDocName = args.input
outputPDFDocName = args.output

#Standard reciepe
document = open(inputPDFDocName, 'rb')
#Create resource manager
rsrcmgr = PDFResourceManager()
# Set parameters for analysis.
laparams = LAParams()
# Create a PDF page aggregator object.
device = PDFPageAggregator(rsrcmgr, laparams=laparams)
interpreter = PDFPageInterpreter(rsrcmgr, device)

parser = PDFParser(document)
doc = PDFDocument(parser)

#Get links and thier positions, and put that info into custom objects
curPage = 0
documentParsed = {}
for page in PDFPage.get_pages(document):
	interpreter.process_page(page)
	# get the pageid order in the document
	pageObjIds.append(page.pageid)
	curPage = getPageNumWithPageObj(page)
	layout = device.get_result()
	# receive the LTPage object for the page.
	urisOnPage = set()
	if page.annots:
		for annotation in page.annots:
			annotationDict = annotation.resolve()
			if annotationDict["Subtype"].name != "Link":
				# Skip over any annotations that are not links
				continue
			position = annotationDict["Rect"]
			uri = ""
			#Sometimes the annotation destinations are stored differently
			if "A" in annotationDict.keys():
				uriDict = annotationDict["A"]
				# This has always been true so far.
				if uriDict["S"].name == "GoTo":
					# Some of my URI's have spaces.
					uri = uriDict["D"].decode("utf-8")
			if "Dest" in annotationDict.keys():
				uri = annotationDict["Dest"].decode("utf-8")

			if uri == "":
				continue
			else:
				uri = uri.replace("(","").replace(")","").strip()
			if uri in linksDict.keys():
				linksDict[uri].addPosition(position, page.pageid)
				linksDict[uri].addObj(annotation)
			else:
				linksDict[uri] = linkDocObj(annotation, uri, position, page.pageid)
				urisOnPage.add(uri)
	urisOnPage = list(urisOnPage)
	urisOnPage.sort()
	print(f"Extracting inline link text on page {curPage}")
	allTextOnPage = []
	for element in layout:
		if type(element) == LTTextBoxHorizontal:
			curLineTextA = getText(element)
			for curLineEE in curLineTextA:
				curLineEE[0] = curLineEE[0].replace("'e","e").replace("'a","a")
				allTextOnPage.append(curLineEE)

	#From https://gist.github.com/lorenzob/f2d79320b4767f434c5c86c985b6de15
	# simple (faster) true/false intersection check
	def intersection(r1,r2):

		X, Y, A, B = r1[0], r1[1], r1[2]-r1[0], r1[3]-r1[1]
		X1, Y1, A1, B1 = r2[0], r2[1], r2[2]-r2[0], r2[3]-r2[1]
		return not (A<X1 or A1<X or B<Y1 or B1<Y)

	def is_close(bbox1, bbox2):
		if intersection(bbox1, bbox1):
				return True
		# how far horizontally are the boxes
		xdiff = abs(max(bbox1[0],bbox2[0]) - min(bbox1[2],bbox2[2]))
		# how far vertically are the centroids of the boxes
		mean_y1=(max_y1+min_y1) / 2.
		mean_y2=(max_y2+min_y2) / 2.
		ydiff = abs(mean_y1 - mean_y2)
		if xdiff < 50 and ydiff < 15:
			return True
		return False

	allTextOnPage = sorted(allTextOnPage,key=lambda x:x[1][0])
	LENGTH = len(allTextOnPage)
	status = np.zeros(LENGTH)
	# compare each box to each other and, if they are close, assign them the same group number
	# Each elements in status correspond to a box and the value is the group it belongs to
	for i, cl1 in enumerate(allTextOnPage):
		x = i
		if i != LENGTH-1:
			for j, cl2 in enumerate(allTextOnPage[i+1:]):
				x = x+1
				if is_close(cnt1[1],cnt2[1]):
					status[x] = status[i]
				else:
					if status[x] == status[i]:
						status[x] = i+1         # let's start a new group

	for i, cl1 in enumerate(allTextOnPage):
		cl1.append(status[i])

	pageSize = page.mediabox
	thresh_image = 255 * np.ones(shape=(pageSize[2], pageSize[3], 3), dtype=np.uint8)
	curPageText = OrderedDict()


	for currentLine in allTextOnPage:
		currentLine[0] = currentLine[0].replace("'e","e").replace("'a","a")
		#Line number removal
		#if prog.match(currentLine[0]) is None:
		xy0 = (math.floor(currentLine[1][0]), math.floor(currentLine[1][1]))
		xy1 = (math.floor(currentLine[1][2]), math.floor(currentLine[1][3]))
		thresh_image = cv2.rectangle(thresh_image, xy0, xy1, (0,0,0), -1)
		LineY0 = math.floor((currentLine[1][1] // 10) * 10)
		addToDict(curPageText,LineY0,currentLine)

	# contourIm = cv2.cvtColor(thresh_image, cv2.COLOR_RGB2GRAY)
	# contours, hierarchy = cv2.findContours(contourIm, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
	# cv2.drawContours(thresh_image, contours, -1, (0,255,0), 3)
	plt.imshow(thresh_image)
	plt.show()
	sys.exit(0)
	curPageText = OrderedDict(sorted(curPageText.items()))
	#So the regular parser is really bad for this,
	#Get rid of all the messiness and use our own
	#stuff
	documentParsed[curPage] = curPageText
	curPageKeys = list(curPageText.keys())
	curPageKeys.sort()
	for uri in urisOnPage:
		possibleLines = []
		foundInlineText = False
		for posO, pageId in linksDict[uri].positions:
			if pageId != page.pageid:
				continue
			boxY = min(math.floor(posO.y0),math.floor(posO.y1))
			boxX = min(math.floor(posO.x0),math.floor(posO.x1))
			boxUX = max(math.floor(posO.x0),math.floor(posO.x1))
			smallKey = 9999999
			for yb in curPageKeys:
				if boxY % 10 != 0:
					if yb > (boxY-10) and yb < smallKey:
						smallKey = yb
				else:
					if yb >= boxY and yb <= smallKey:
						smallKey = yb
			#print(boxY, " -> ", smallKey)
			lineOs = curPageText[smallKey]
			for lineP in lineOs:
				lineX0 = math.floor(lineP[1][0])
				lineX1 = math.floor(lineP[1][2])
				charWidth = math.floor(lineP[2])
				lineLen = len(lineP[0])
				if (lineX0 <= (boxX+1)) and ((boxUX-1) <= lineX1):
					#Now that we found the correct line, we must pull out the
					#text, to do this we approximate the start and end of the
					#substring, then find the next closest whitespace to those
					#approximations
					reSpaceF = re.finditer("\s+", lineP[0])
					spaceIndes = [space.start() for space in reSpaceF]
					spaceIndes.sort()
					startInd = max((abs(boxX - lineX0) // charWidth),0)
					endInd = min((abs(boxUX - lineX0) // charWidth) + 1,lineLen)
					spaceIndes.insert(0, 0)
					spaceIndes.append(lineLen)
					closestStart = -999999
					closestEnd = 999999
					for ind in spaceIndes:
						if ind >= endInd and ind < closestEnd:
							closestEnd = ind
						if ind <= startInd and ind > closestStart:
							closestStart = ind
					inlineTextB = lineP[0][closestStart:closestEnd]
					if inlineTextB == "":
						inlineTextB = lineP[0]
					possibleLines.append(inlineTextB)
					linksDict[uri].addAssocText(inlineTextB)
					linksDict[uri].increaseText()
					foundInlineText = True
		if not foundInlineText:
			print("Error! No inline text found for ",uri, " at ",posO, " please input the inline citation")
			ansss = input(">")
			linksDict[uri].addAssocText(inlineTextB)
			linksDict[uri].increaseText()

#The destinations of the links in the link object are
#names which reference destinations in the document catalog
#so we need to parse the "Dest" portion of the document
#catalog and connect it to a link above
names = dict_value(doc.catalog["Names"])
dests = dict_value(names["Dests"])
destTree = destTreeNode(dests)
destD = {}


leafList = []
getbottomNodes(destTree,leafList)

for y in leafList:
	nA = list(y.selfRep["Names"])
	curkey = ""
	#At this level they are in a list of [<key> <value> <key 2> <value 2> ...]
	for nI, nn in enumerate(nA):
		if not (nI % 2):
			curkey = nA[nI].decode("utf-8")
		else:
			try:
				destD[curkey] = nA[nI].resolve()["D"]
			except:
				continue

testK = list(destD.keys())[0]

curDD = destD[testK][0].resolve()
#Go to the top of the Dest tree
while True:
	if "Parent" in curDD.keys():
		curDD = curDD["Parent"].resolve()
	else:
		break

#Go down the tree and figure out which object refers to which
#page number
pageTree = destTreeNode(curDD)
analyzeKids(pageTree)

#Finally figure out which page those inline links go to.
#This is so we don't analyze the entire document and
#get even more errors and false positives
#Unfortuantly the "XYZ" part of the destination object
#refers to the position of top-left corner of the rendering window
#when clicked, so is useless for our purposes and will have to
#deal with the entire page (which is fine)
for linkName, linkDest in destD.items():
	linkDestContents = linkDest[0].resolve()["Contents"]
	destPageNum = 0
	if type(linkDestContents) == PDFObjRef:
		destPageNum = getPageNumber(linkDestContents)
	elif type(linkDestContents) == list:
		destPageNum = getPageNumber(linkDestContents[0])
	else:
		print("ERROR! Unknown type for link destination")
		print(linkName)
		print(linkDestContents)
		sys.exit(0)
	try:
		linksDict[linkName].setDestPage(destPageNum)
	except KeyError:
		print(f"Warning! {linkName} does not have an associated GOTO link in document")

#In most papers, cite links are actually preceeded by "cite"
citePageNums = set([x.getDestPage() for x in linksDict.values() if "cite" in x.getURI()])

# Troubleshooting output
print("Citation Page Numbers : ",citePageNums)

#Line number removal
#prog = re.compile("^\s*\d{2,4}\s*$")

finalCites = []
#Now that we know where the citations are, lets parse that page
for citePageNum in citePageNums:
	print("Attempting to parse citations on page ",citePageNum)
	#Get all the lines of text on that page
	refPageText = list(documentParsed[citePageNum].values())
	refPageText = [item for sublist in refPageText for item in sublist]
	refPageText = sorted(refPageText, key=lambda x: x[1][1], reverse=True)
	#Split the page into columns
	pageColumns = [textColumn(refPageText.pop())]

	for part in refPageText:
		addChildIn = -1
		for testIn, col in enumerate(pageColumns):
			if col.inCol(part):
				addChildIn = testIn
		if addChildIn > -1:
			pageColumns[addChildIn].addChild(part)
		else:
			pageColumns.append(textColumn(part))

	#If a line was split into multiple LTTextBoxHorizontals
	#then this entire thing breaks, so lets do a check for that
	# and merge any LTTextBoxHorizontals with the same y0
	#This step also includes sorting by height, which makes
	#parsing much easier
	for tColI in range(len(pageColumns)):
		pageColumns[tColI].checkForBadLines()

	#Split each column of text on the page into blocks
	#of text with each block representing a continuous string of
	#information
	colN = 1
	for tCol in pageColumns:
		colLineH = int(tCol.getLineHeight(1.5))
		print(f"Page {citePageNum}; Column {colN} has a height thresh of {colLineH}")
		#First we need to split this column into paragraphs;
		#So any large gap will create a break
		lastHeight = 9999
		curPara = []
		paragraphs = []
		#Only works because organized by y above
		for chilI, chil in enumerate(tCol.getChildren()):
			curChilHeight = int(chil[1][1])
			lineHDiff = abs(curChilHeight - lastHeight)
			if (lineHDiff > colLineH) and (len(curPara) > 0):
				paragraphs.append(curPara)
				curPara = []
			curPara.append(chil)
			lastHeight = colLineH
		paragraphs.append(curPara)
		colN += 1
		for paragraph in paragraphs:
			#We need to know the various indentation levels
			#of the paragraph
			tColLevels = set()
			for chilI, chil in enumerate(paragraph):
				tColLevels.add(int(chil[1][0]))

			tColLevels = list(tColLevels)
			tColLevels.sort()

			lastHeight = 9999
			pastLevel = 99
			chilBlocks = []
			curChilBlock = -1
			for chilI, chil in enumerate(paragraph):
				curChilHeight = int(chil[1][1])
				lineHDiff = abs(curChilHeight - lastHeight)
				curLevel = tColLevels.index(int(chil[1][0]))
				#All the ways the line can be the same,
				#needed because indentation is complicated in
				#how it relates to citations
				if (lineHDiff < colLineH):
					chilBlocks[curChilBlock].append(chil)
				elif ((curLevel < pastLevel) and (curLevel == 0)):
					chilBlocks.append([chil])
					curChilBlock += 1
				elif (pastLevel == 0) and (curLevel == 0):
					chilBlocks.append([chil])
					curChilBlock += 1
				else:
					try:
						chilBlocks[curChilBlock].append(chil)
					except IndexError:
						#The paragraph starts indented
						chilBlocks.append([chil])
						curChilBlock += 1
				pastLevel = curLevel
				lastHeight = curChilHeight
			#Add blocks to the final citations list
			for block in chilBlocks:
				finalCites.append(unidecode("".join([x[0].replace("- ","").replace("  "," ") for x in block])))
finalCites = [x for x in finalCites if x != ""]

cleanedCites = []
#Some cleaning, if a line has an inline citation in it
#then it is not itself a full citation
allInLineText = []
for linkKey, linkObj in linksDict.items():
	for inlineText in linkObj.getAllText():
		#Basic cleaning of the inline text, ensure a year is in it
		if re.search("\d{4}[ab]?",inlineText):
			inlineText = inlineText.strip()
			allInLineText.append(inlineText)

for citeLine in finalCites:
	citeLine = citeLine.strip()
	if citeLine == "":
		continue
	#Basic cleaning of the line text, ensure a year is in it
	if re.search("\d{4}[ab]?",citeLine):
		isClean = True
		for inlineText in allInLineText:
			if inlineText in citeLine:
				isClean = False
		if isClean:
			cleanedCites.append(citeLine)

finalCites = cleanedCites
finalCites.sort()

print("")
print("--------------------------")
print("List of extracted citations")
print("\n".join(finalCites))
print("--------------------------")
with open("input.txt","w") as fp:
	fp.write(";;;\n")
	fp.write("\n".join(finalCites))

#Use the anystyle.io CLI to parse the citations
jsonStr = subprocess.run(["anystyle","--stdout","-f","json,txt","parse","input.txt"], stdout=subprocess.PIPE).stdout.decode("utf-8")
jsonStrD, jsonStrIn = jsonStr.split(";;;")
citeParsed = json.loads(jsonStrD)
inA = jsonStrIn.split("\n")

preRepRules = [["and","&"]]
postRepRules = []
usingPost = False
try:
	with open("replace_rules.txt","r", errors = 'ignore') as fp:
		for line in fp:
			line = line.strip()
			if line == ";;;":
				usingPost = True
			else:
				lineArr = line.split("->")
				lineArr = [x.strip() for x in lineArr]
				if len(lineArr) == 1:
					lineArr = [lineArr[0],""]
				if usingPost:
					postRepRules.append(lineArr)
				else:
					preRepRules.append(lineArr)
except FileNotFoundError:
	pass

#Lets look at all the text scraped from
#inline citations and turn one of them into a
#author part and year part; then search all of
#the unparsed citations to find that author and
#year
print("Rules from replace_rules.txt")
print("Pre-rules : ", preRepRules)
print("Post-rules : ", postRepRules)
print("--------------------------")
print("")

preRepRules = [x for x in preRepRules if x != [""]]
postRepRules = [x for x in postRepRules if x != [""]]

grabbedCites = set()
citeFind = re.compile("(['A-Za-z0-9.\- ,&]+)(?:[.+ ]+)\(?(\d{4}[ab]?)")
for linkKey, linkObj in linksDict.items():
	print(linkKey)
	print(linkObj.getAllText())
	citeFindstr = set()
	textCont = stitchString(linkObj.getAllText())
	textCont = unidecode(textCont)
	if len(preRepRules) > 0:
		for rule in preRepRules:
			textCont = textCont.replace(rule[0],rule[1])
	for group in citeFind.findall(textCont):
		for part in group:
			part = part.replace("et al.","").strip()
			part = " ".join(list(part.split(" ")))
			if len(postRepRules) > 0:
				for rule in postRepRules:
					part = part.replace(rule[0],rule[1])
			part = part.strip()
			citeFindstr.add(part)
	yearPart = ""
	authorPart = ""
	unparseCite = ""
	for citePart in citeFindstr:
		if re.search("\d{4}[ab]?",citePart):
			yearPart = citePart.strip().replace("a","").replace("b","")
		else:
			authorPart = citePart.strip()
	if (yearPart == "") and (authorPart == ""):
		continue
	authors = [x.strip() for x in re.split("[,&]",authorPart)]
	authors = [x for x in authors if x != ""]
	citationDict = {}
	corI = -1
	for citeI, unProcessedCite in enumerate(inA):
		unProcessedCite = unProcessedCite.strip()
		#Each in-line citation only refers to one citation
		if citeI in grabbedCites:
			continue

		authBool = [(authorP in unProcessedCite) for authorP in authors]
		if (sum(authBool) == len(authBool)) and (yearPart in unProcessedCite):
			#Make sure one of the authors is the first author
			lowestInd = 999999
			for auth in authors:
				lowInd = unProcessedCite.index(auth)
				if lowInd < lowestInd:
					lowestInd = lowInd
			if lowestInd > 2:
				continue
			corI = citeI
			unparseCite = inA[citeI]
			citationDict = citeParsed[citeI]
			break
	if unparseCite == "":
		print("Unable to connect text from document : ",linkObj.getAllText()," to a citation.")
		print("Failed Author(s) String : ",authors)
		print("Failed Year String : ", yearPart)
		print("Please edit replace_rules.txt to clean up the extracted text")
		ans = input("Manually input citation (if empty it will quit)>")
		if ans == "":
			sys.exit(0)
		else:
			unparseCite = ans
	else:
		print("Connected the text from document : ",linkObj.getAllText()," to ", unparseCite, " using ",authors," and ",yearPart)
	linkObj.author = authorPart
	linkObj.year = yearPart
	linkObj.setPaperObj(citationDict)
	linkObj.unparseCite = unparseCite
	grabbedCites.add(corI)

print("--------------------------------------------------")
breakStop = 0
for linkKey, linkObj in linksDict.items():
	unparseStr = linkObj.unparseCite
	citeParse = linkObj.papObj
	if citeParse is None:
		print(f"Error! {linkKey} has no citation! ",linkObj)
		continue
	adsSearchString = ""
	print(unparseStr)
	print(citeParse)
	if len(list(citeParse.keys())) == 0:
		continue

	#Now lets take the parsed parts of the citation and turn it
	#into an ADS search query
	adsParts = {"author":""}
	#3 authors is enough to narrow it down quite a bit
	maxAuthors = 3
	authorCount = 1
	for authorD in citeParse["author"]:
		if ("family" in authorD.keys()) and ('given' in authorD.keys()):
			if authorD["family"] == "Collaboration":
				continue

			authName = authorD['family']
			authGiven = authorD['given']
			authName = authName.replace(",","").strip()
			authGiven = authGiven.replace(",","").strip()
			if len(authName) == 1:
				authName = authName + "."
			if len(authGiven) == 1:
				authGiven = authGiven + "."
			if "particle" in authorD.keys():
				authName = authName["particle"] + " " + authName

			# This is because the parser gets really confused with names
			# like A. B. Testman so we need to move the one letter parts
			# to the front of the other parts, preserving order
			failSafe = ""
			for citePart in unparseStr.split(","):
				nameParts = f"{authName} {authGiven}".split(" ")
				isInCitePart = [isNone(re.search(x,citePart)) for x in nameParts]
				if sum(isInCitePart) == len(nameParts):
					oneLetterPart = ""
					nonOneLetterPart = ""
					unParseParts = [x.strip() for x in citePart.split()]
					for unParsePart in unParseParts:
						npp = unParsePart.replace(".","")
						if len(npp) == 1:
							oneLetterPart += unParsePart + " "
						else:
							nonOneLetterPart += unParsePart + " "
					citePart = f"{oneLetterPart}{nonOneLetterPart}".strip()
					failSafe = f" OR \"{citePart}\""
					failSafe = " ".join(failSafe.split())
					break
			#Author Names are complicated, how it was parsed and how we are putting it back together
			#could yield wrong formats. To do it systemically, we attempt all formats and hope
			#one is correct
			adsParts["author"] += f" author:(\"{authName} {authGiven}\" OR \"{authGiven} {authName}\"{failSafe})"
			authorCount += 1
			if authorCount > maxAuthors:
				break

	if 'date' in citeParse.keys():
		adsParts["year"] = f" year:{citeParse['date'][0]}"

	if 'volume' in citeParse.keys():
		volNum = citeParse['volume'][0].split(',')[0].lstrip("0")
		adsParts["volume"] = f" volume:{volNum}"

	if 'container-title' in citeParse.keys():
		testBibstem = citeParse['container-title'][0]
		if testBibstem == "Science":
			testBibstem = "sci"
		if testBibstem == "ApJSS":
			testBibstem = "ApJS"
		if citeParse['type'] == 'article-journal':
			adsParts["bibstem"] = f" bibstem:{testBibstem}"

	if "pages" in citeParse.keys():
		orgPage = citeParse['pages'][0]
		orgPage = re.findall("\d+",orgPage)[0]
		pageCharCheck = re.compile(f"[A-Za-z]?{orgPage}[A-Za-z]?(?:\.?)")
		pageNumP = pageCharCheck.findall(unparseStr)[0].strip()
		pageNumP = pageNumP.lstrip("0")
		orgPage = orgPage.lstrip("0")
		adsParts["page"] = f" (page:{orgPage} OR page:{pageNumP})"

	#These requires messy handling because they may contain /
	#But with a these, they identify only one paper
	#so we can ignore everything but them
	papers = []
	if "url" in citeParse.keys():
		urlSearch = f" {citeParse['url'][0]}"
		response = ads_search(urlSearch)
		try:
			response.raise_for_status()
			papers = na.ADS._parse_response(response.json())
			print(urlSearch)
		except:
			pass

	if "arxiv" in citeParse.keys():
		arxivSearch = f" arxiv:{citeParse['arxiv'][0]}"
		response = ads_search(arxivSearch)
		try:
			response.raise_for_status()
			papers = na.ADS._parse_response(response.json())
			print(arxivSearch)
		except:
			pass

	if "doi" in citeParse.keys():
		doiSearch = f'doi:\"{citeParse["doi"][0]}\"'
		response = ads_search(doiSearch)
		try:
			response.raise_for_status()
			papers = na.ADS._parse_response(response.json())
			print(doiSearch)
		except:
			pass

	if len(papers) == 0:
		doAttemptChain = True
		try:
			adsSearchString = "".join(list(adsParts.values())).strip()
			papers = na.ADS.query_simple(adsSearchString)
			if len(papers) == 1:
				doAttemptChain = False
				print(adsSearchString)
		except Exception as e:
			print(e)

		if doAttemptChain:
			retPapers, adsQ = attempt_ads(adsParts)
			if (retPapers is not None) and ((len(retPapers) < len(papers)) or (len(papers) == 0)):
				papers = retPapers
				adsSearchString = adsQ
			print(adsSearchString)

	if len(papers) > 1:
		print("----------------------------------")
		print("More than 1 paper!")
		paperTitles = [x["title"] for x in papers]
		paperTitles.append("None of these")
		selectItem = arraySelector(paperTitles, "Please select the correct paper")
		if (selectItem == "None of these"):
			papers = []
		else:
			selectItem = paperTitles.index(selectItem)
			papers = [papers[selectItem]]
		print("----------------------------------")
	if len(papers) > 0:
		print(papers[0]["title"])
		print(f"https://ui.adsabs.harvard.edu/abs/{papers[0]['bibcode']}/abstract")
		linksDict[linkKey].setPaperLink(f"https://ui.adsabs.harvard.edu/abs/{papers[0]['bibcode']}/abstract")
	else:
		print("No papers found, tested string : ",adsSearchString)
		corLink = input("Please input the correct link > ")
		linksDict[linkKey].setPaperLink(corLink)
	print("")
	breakStop += 1
	time.sleep(3)

document.close()

pdfrwpdf = pdfrw.PdfReader(inputPDFDocName)  # Load the pdf
new_pdf = pdfrw.PdfWriter()  # Create an empty pdf

for pdfrwpage in pdfrwpdf.pages:  # Go through the pages
	# Links are in Annots, but some pages don't have links so Annots returns None
	for pdfrwannot in pdfrwpage.Annots or []:
		if (pdfrwannot.Subtype != "/Link") and (pdfrwannot.A.S != "/GoTo"):
			# Skip over any annotations that are not goto links
			continue
		try:
			old_url = pdfrwannot.A.D.replace("(","").replace(")","")
		except AttributeError:
			print("Unable to process annotation")
			print(pdfrwannot)
			continue
		papLink = ""
		if old_url in linksDict.keys():
			papLink = linksDict[old_url].getPaperLink()
		else:
			print("Error!", old_url," did not have an associated processed citation")
		if papLink == "":
			continue
		# GOTO Annotation Example:
		#{'/Type': '/Annot', '/Subtype': '/Link', '/A': {'/D': '(cite.Fong21)',
		# '/S': '/GoTo'}, '/Border': ['0', '0', '0'], '/C': ['0', '1', '0'],
		# '/H': '/I', '/Rect': ['524.058', '109.413', '543.983', '119.408']}
		#
		# External Link Example:
		#{'/Type': '/Annot', '/Subtype': '/Link', '/A': {'/Type': '/Action',
		# '/S': '/URI', '/URI': '(https://casa.nrao.edu/)'},
		#'/Border': ['0', '0', '0'], '/C': ['0', '1', '1'], '/H': '/I',
		# '/Rect': ['311.701', '45.854', '381.432', '57.898']}
		new_url = pdfrw.objects.pdfstring.PdfString("("+papLink+")")
		new_type = pdfrw.objects.pdfstring.PdfString("/URI")
		new_action = pdfrw.objects.pdfstring.PdfString("/Action")
		# Override the URL with ours
		pdfrwannot.A.D = None
		pdfrwannot.A.Type = new_action
		pdfrwannot.A.S = new_type
		pdfrwannot.A.URI = new_url
		pdfrwannot.C = ['0','1','1']
	new_pdf.addpage(pdfrwpage)

new_pdf.write(outputPDFDocName)

print("Created pdf ", outputPDFDocName)
