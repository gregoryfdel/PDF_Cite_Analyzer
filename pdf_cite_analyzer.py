from pdfminer.layout import LAParams
from pdfminer.pdfinterp import PDFResourceManager
from pdfminer.converter import PDFPageAggregator
from pdfminer.pdfpage import PDFPage
from pdfminer.layout import LTTextBoxHorizontal
from pdfminer.pdfinterp import PDFPageInterpreter
from pdfminer.pdfdocument import PDFDocument
from pdfminer.pdfparser import PDFParser
from pdfminer.layout import LTChar
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

from astroquery import nasa_ads as na
# if you don't store your token as an environment variable
# or in a file, give it here
adsToken = ''

if adsToken == '':
	try:
		with open("ads_token.txt",'r') as fp:
			for line in fp:
				token = line.strip()
	except:
		pass

na.ADS.TOKEN = adsToken
# by default, the top 10 records are returned, sorted in
# reverse chronological order. This can be changed

# change the number of rows returned
na.ADS.NROWS = 20
# change the sort order
na.ADS.SORT = 'bibcode desc'
# change the fields that are returned (enter as strings in a list)
# We only need the title and bibcode
na.ADS.ADS_FIELDS = ['title', 'bibcode']

linksDict = {}
pageObjIds = []
pageIds = []

class Link(object):
	__slots__ = 'prev', 'next', 'key', '__weakref__'

#Used to clean up inline citations
class OrderedSet(collections.MutableSet):
	'Set the remembers the order elements were added'
	# Big-O running times for all methods are the same as for regular sets.
	# The internal self.__map dictionary maps keys to links in a doubly linked list.
	# The circular doubly linked list starts and ends with a sentinel element.
	# The sentinel element never gets deleted (this simplifies the algorithm).
	# The prev/next links are weakref proxies (to prevent circular references).
	# Individual links are kept alive by the hard reference in self.__map.
	# Those hard references disappear when a key is deleted from an OrderedSet.

	def __init__(self, iterable=None):
		self.__root = root = Link()		 # sentinel node for doubly linked list
		root.prev = root.next = root
		self.__map = {}					 # key --> link
		if iterable is not None:
			self |= iterable

	def __len__(self):
		return len(self.__map)

	def __contains__(self, key):
		return key in self.__map

	def add(self, key):
		# Store new key in a new link at the end of the linked list
		if key not in self.__map:
			self.__map[key] = link = Link()
			root = self.__root
			last = root.prev
			link.prev, link.next, link.key = last, root, key
			last.next = root.prev = proxy(link)

	def discard(self, key):
		# Remove an existing item using self.__map to find the link which is
		# then removed by updating the links in the predecessor and successors.
		if key in self.__map:
			link = self.__map.pop(key)
			link.prev.next = link.next
			link.next.prev = link.prev

	def __iter__(self):
		# Traverse the linked list in order.
		root = self.__root
		curr = root.next
		while curr is not root:
			yield curr.key
			curr = curr.next

	def __reversed__(self):
		# Traverse the linked list in reverse order.
		root = self.__root
		curr = root.prev
		while curr is not root:
			yield curr.key
			curr = curr.prev

	def pop(self, last=True):
		if not self:
			raise KeyError('set is empty')
		key = next(reversed(self)) if last else next(iter(self))
		self.discard(key)
		return key

	def __repr__(self):
		if not self:
			return '%s()' % (self.__class__.__name__,)
		return '%s(%r)' % (self.__class__.__name__, list(self))

	def __eq__(self, other):
		if isinstance(other, OrderedSet):
			return len(self) == len(other) and list(self) == list(other)
		return not self.isdisjoint(other)

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
	def __init__(self,firstElem,thres=15.0):
		self.minX = firstElem[1][0]
		self.maxX = firstElem[1][2]
		self.threshold = thres
		self.children = [firstElem]
		self.flag = 0

	def inCol(self,testEle):
		if (testEle[1][0] <= (self.maxX + self.threshold)) and (self.minX <= (testEle[1][2] - self.threshold)):
			if testEle[1][0] < self.minX:
				self.minX = testEle[1][0]
			if testEle[1][2] > self.maxX:
				self.maxX = testEle[1][2]
			return True
		return False

	def addChild(self,testEle):
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

	def getLineHeight(self,eps=1.5):
		if len(self.children) == 0:
			print("Please add children")
			return -1
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




#Use element position syntax while
#using the list position format
#that the objects in this script use
class posObj:
	def __init__(self,pos):
		self.posList = pos
		self.x0 = pos[0]
		self.y0 = pos[1]
		self.x1 = pos[2]
		self.y1 = pos[3]

#The mega object which needs to
#store data about itself due to the number of
#steps needed between extracting the inline citations
#connecting them to a citation on the citation page
#parsing the citation, then searching ADS for
#that citation; then finally replacing the
#GOTO inline links with an ADS link
class linkObj:
	def __init__(self, annoObj, uri, pos, pageid):
		self.origObjs = [annoObj]
		self.gotoLoc = uri
		self.assocText = [""]
		self.assocTextIn = 0
		self.positions = [[posObj(pos),pageid]]
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
		self.positions.append([posObj(pos),pageid])

	def linkContains(self, element, pageid):
		if not type(element) is LTChar:
			return False
		for testPos in self.positions:
			if pageid != testPos[1]:
				continue
			testLoc = testPos[0]
			if (element.x0 <= testLoc.x1) and (testLoc.x0 <= element.x1) and (element.y0 <= testLoc.y1) and (testLoc.y0 <= element.y1):
				return True
		return False

	def addAssocText(self,text):
		self.assocText[self.assocTextIn] += text

	def increaseText(self):
		self.assocText.append("")
		self.assocTextIn += 1

	def getAllText(self):
		return self.assocText

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
		for char in line._objs:
			if type(char) == LTChar:
				curLine += char.get_text()
			else:
				curLine += " "
		retLines.append((curLine,[line.x0,line.y0,line.x1,line.y1]))
		curLine = ""
	return retLines


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
for page in PDFPage.get_pages(document):
	interpreter.process_page(page)
	# receive the LTPage object for the page.
	if page.annots:
		for annotation in page.annots:
			annotationDict = annotation.resolve()
			if annotationDict["Subtype"].name != "Link":
				# Skip over any annotations that are not links
				continue
			position = annotationDict["Rect"]
			uriDict = annotationDict["A"]
			# This has always been true so far.
			if uriDict["S"].name == "GoTo":
				# Some of my URI's have spaces.
				uri = uriDict["D"].decode("utf-8")
				if uri in linksDict.keys():
					linksDict[uri].addPosition(position, page.pageid)
					linksDict[uri].addObj(annotation)
				else:
					linksDict[uri] = linkObj(annotation, uri, position, page.pageid )

# get the pageid order in the document
for page in PDFPage.get_pages(document):
	interpreter.process_page(page)
	pageObjIds.append(page.pageid)

# now that we have all the links in the document
# lets go back and figure out which text is inside them
prevChar = None
for page in PDFPage.get_pages(document):
	interpreter.process_page(page)
	# receive the LTPage object for the page.
	layout = device.get_result()
	for linkKey in linksDict.keys():
		for element in layout:
			changedLinkObj = False
			if type(element) == LTTextBoxHorizontal:
				for line in element._objs:
					for char in line._objs:
						if linksDict[linkKey].linkContains(char, page.pageid):
							newChar = char.get_text()
							changedLinkObj = True
							linksDict[linkKey].addAssocText(newChar)
						elif linksDict[linkKey].linkContains(prevChar, page.pageid):
							changedLinkObj = True
							linksDict[linkKey].addAssocText(" ")
						else:
							pass
						prevChar = char
			if changedLinkObj:
				linksDict[linkKey].increaseText()

#The destinations of the links in the link object are
#names which reference destinations in the document catalog
#so we need to parse the "Dest" portion of the document
#catalog and connect it to a link above
names = dict_value(doc.catalog["Names"])
dests = dict_value(names["Dests"])
destTree = destTreeNode(dests)
destD = {}

for x in destTree.kids:
	for y in x.kids:
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
	for page in PDFPage.get_pages(document):
		interpreter.process_page(page)
		if getPageNumWithPageObj(page) != citePageNum:
			continue
		refPageText = []
		print("On citation page, attempting to parse")
		layout = device.get_result()
		for element in layout:
			if type(element) == LTTextBoxHorizontal:
				curLineTextA = getText(element)
				for curLineText in curLineTextA:
					#Line number removal
					#if prog.match(curLineText[0]) is None:
					refPageText.append(curLineText)
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

		for tColI in range(len(pageColumns)):
			pageColumns[tColI].organizeChildren()
			#print("----------------------------------")
			#print(f" Column {tColI}")
			#print("----------------------------------")
			#for child in pageColumns[tColI].getChildren():
			#	print(child)
		#print("")
		#print("")
		#If a line was split into multiple LTTextBoxHorizontals
		#then this entire thing breaks, so lets do a check for that
		# and merge any LTTextBoxHorizontals with the same y0
		#which includes sorting
		for tColI in range(len(pageColumns)):
			pageColumns[tColI].checkForBadLines()

		#Split the page into blocks
		for tCol in pageColumns:
			heightThresh = int(tCol.getLineHeight())
			tColLevels = set()
			for chilI, chil in enumerate(tCol.getChildren()):
				tColLevels.add(int(chil[1][0]))

			tColLevels = list(tColLevels)
			tColLevels.sort()

			lastHeight = 9999
			pastLevel = 99
			chilBlocks = []
			curChilBlock = -1
			for chilI, chil in enumerate(tCol.getChildren()):
				curChilHeight = int(chil[1][1])
				lineHDiff = abs(curChilHeight - lastHeight)
				curLevel = tColLevels.index(int(chil[1][0]))
				if (lineHDiff > 1) and ((curLevel < pastLevel) or (lineHDiff > heightThresh)):
					chilBlocks.append([chil])
					curChilBlock += 1
				else:
					chilBlocks[curChilBlock].append(chil)
				pastLevel = curLevel
				lastHeight = curChilHeight
			#Add blocks to the final citations list
			for block in chilBlocks:
				finalCites.append("".join([x[0] for x in block]))

finalCites.sort()

print("")
print("--------------------------")
print("List of extracted citations")
print("\n".join(finalCites))
print("--------------------------")

with open("input.txt","w") as fp:
	fp.write(";;;\n")
	fp.write("\n".join(finalCites))

jsonStr = subprocess.run(["anystyle","--stdout","-f","json,txt","parse","input.txt"], stdout=subprocess.PIPE).stdout.decode("utf-8")
jsonStrD, jsonStrIn = jsonStr.split(";;;")
citeParsed = json.loads(jsonStrD)

inA = jsonStrIn.split("\n")

preRepRules = []
postRepRules = []
usingPost = False
try:
	with open("replace_rules.txt","r", errors = 'ignore') as fp:
		for line in fp:
			line = line.strip()
			if line == ";;;":
				usingPost = True
			else:
				if usingPost:
					postRepRules.append(line.split(" -> "))
				else:
					preRepRules.append(line.split(" -> "))
except FileNotFoundError:
	pass

print("Rules from replace_rules.txt")
print("Pre-rules : ", preRepRules)
print("Post-rules : ", postRepRules)
print("--------------------------")
print("")
citeFind = re.compile("([A-Za-z0-9.\- ]+)(?:[.+ ]+|&.+)\(?(\d{4}[ab]?)")
for linkKey, linkObj in linksDict.items():
	citeFindstr = set()
	for textCont in linkObj.getAllText():
		if len(preRepRules) > 0:
			for rule in preRepRules:
				textCont = textCont.replace(rule[0],rule[1])
		for group in citeFind.findall(textCont):
			for part in group:
				part = part.replace("et al.","").strip()
				part = " ".join(list(OrderedSet(part.split(" "))))
				if len(postRepRules) > 0:
					for rule in postRepRules:
						part = part.replace(rule[0],rule[1])
				part = part.strip()
				citeFindstr.add(part)
	yearPart = ""
	authorPart = ""
	unparseCite = ""
	for citePart in citeFindstr:
		if re.match("\d{4}[ab]?",citePart):
			yearPart = citePart.strip().replace("a","").replace("b","")
		else:
			authorPart = citePart.strip()
	if (yearPart == "") and (authorPart == ""):
		continue
	citationDict = {}
	for citeI, unProcessedCite in enumerate(inA):
		if len(unProcessedCite) > 500:
			continue
		if (authorPart in unProcessedCite) and (yearPart in unProcessedCite):
			unparseCite = inA[citeI]
			citationDict = citeParsed[citeI]
	if unparseCite == "":
		print("Unable to connect text from document : ",linkObj.getAllText()," to a citation.")
		print("Failed Author String : ",authorPart)
		print("Failed Year String : ", yearPart)
		print("Please edit replace_rules.txt to clean up the extracted text and make the author and year clear.")
		while True:
			ans = input("Would you like to quit [y/n] >")
			if ans == "y":
				sys.exit(0)
			else:
				break
	else:
		print("Connected the text from document : ",linkObj.getAllText()," to ", unparseCite)
	linkObj.author = authorPart
	linkObj.year = yearPart
	linkObj.setPaperObj(citationDict)
	linkObj.unparseCite = unparseCite

print("--------------------------------------------------")
breakStop = 0
for linkKey, linkObj in linksDict.items():
	unparseStr = linkObj.unparseCite
	citeParse = linkObj.papObj
	if citeParse is None:
		print(f"Error! {linkKey} has no citation!")
		continue
	adsSearchString = ""
	print(unparseStr)
	print(citeParse)
	if len(list(citeParse.keys())) == 0:
		continue

	adsParts = {"author":""}
	for authorD in citeParse["author"]:
		if "family" in authorD.keys():
			if authorD["family"] == "Collaboration":
				continue
			particleAuth = ""
			if "particle" in authorD.keys():
				particleAuth = authorD["particle"] + " "
			adsParts["author"] += f" author:\"{particleAuth}{authorD['family']}, {authorD['given']}\""

	if 'date' in citeParse.keys():
		adsParts["year"] = f" year:{citeParse['date'][0]}"

	if 'volume' in citeParse.keys():
		adsParts["volume"] = f" volume:{citeParse['volume'][0].split(',')[0]}"

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
		pageCharCheck = re.compile(f"[A-Z]?{orgPage}[A-Z]?")
		pageNumP = pageCharCheck.findall(unparseStr)[0].strip()
		adsParts["page"] = f" (page:{orgPage} OR page:{pageNumP})"

	if "url" in citeParse.keys():
		citeUrl = citeParse['url'][0]
		adsParts["arxiv"] = f" {citeUrl}"

	if "arxiv" in citeParse.keys():
		adsParts["arxiv"] = f" arxiv:{citeParse['arxiv'][0]}"
	papers = []
	try:
		if "arxiv" in adsParts.keys():
			adsSearchString = adsParts["arxiv"].strip()
		else:
			adsSearchString = "".join(list(adsParts.values()))
		papers = na.ADS.query_simple(adsSearchString)
		print(adsSearchString)
	except:
		attempts = [["page"],["bibstem"],["volume"],["volume","page"],["volume","page","bibstem"]]
		for attempt in attempts:
			try:
				time.sleep(3)
				attAdsParts = {}
				for attK, attV in adsParts.items():
					if not attK in attempt:
						attAdsParts[attK] = attV
				adsSearchString = "".join(list(attAdsParts.values()))
				papers = na.ADS.query_simple(adsSearchString)
				print(adsSearchString)
				break
			except:
				continue
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
		old_url = pdfrwannot.A.D.replace("(","").replace(")","")
		papLink = linksDict[old_url].getPaperLink()
		if papLink == "":
			continue
		new_url = pdfrw.objects.pdfstring.PdfString("("+papLink+")")
		new_type = pdfrw.objects.pdfstring.PdfString("/URI")
		# Override the URL with ours
		pdfrwannot.A.S = new_type
		pdfrwannot.A.URI = new_url
	new_pdf.addpage(pdfrwpage)

new_pdf.write(outputPDFDocName)
