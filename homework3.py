"""
Query format:   Each query will be a single literal of the form Predicate(Constant_Arguments) or
                ~Predicate(Constant_Arguments) and will not contain any variables. Each predicate will have
                between 1 and 25 constant arguments. Two or more arguments will be separated by commas.
KB format:      Each sentence in the knowledge base is written in one of the following forms:
        1) An implication of the form p1 ∧ p2 ∧ ... ∧ pm ⇒ q, where its premise is a conjunction of
           literals and its conclusion is a single literal. Remember that a literal is an atomic sentence
           or a negated atomic sentence.
        2) A single literal: q or ~q

Note:
        1. & denotes the conjunction operator.
        2. | denotes the disjunction operator. It will not appear in the queries nor in the KB given as
        input. But you will likely need it to create your proofs.
        3. => denotes the implication operator.
        4. ~ denotes the negation operator.
        5. No other operators besides &, =>, and ~ are used in the knowledge base.
        6. There will be no parentheses in the KB except as used to denote arguments of predicates.
        7. Variables are denoted by a single lowercase letter.
        8. All predicates (such as HighBP) and constants (such as Alice) are case sensitive
        alphabetical strings that begin with uppercase letters.
        9. Each predicate takes at least one argument. Predicates will take at most 25 arguments. A
        given predicate name will not appear with different number of arguments.
        10. There will be at most 10 queries and 100 sentences in the knowledge base.
        11. See the sample input below for spacing patterns.
        12. You can assume that the input format is exactly as it is described.
        13. There will be no syntax errors in the given input.
        14. The KB will be true (i.e., will not contain contradictions).

Format for input.txt
        <N = NUMBER OF QUERIES>
        <QUERY 1>
        …
        <QUERY N>
        <K = NUMBER OF GIVEN SENTENCES IN THE KNOWLEDGE BASE>
        <SENTENCE 1>
        …
        <SENTENCE K>
        The first line contains an integer N specifying the number of queries. The following N lines contain
        one query per line. The line after the last query contains an integer K specifying the number of
        sentences in the knowledge base. The remaining K lines contain the sentences in the knowledge
        base, one sentence per line.

Format for output.txt:
        For each query, determine if that query can be inferred from the knowledge base or not, one
        query per line:
        <ANSWER 1>
        …
        <ANSWER N>
        Each answer should be either TRUE if you can prove that the corresponding query sentence is
        true given the knowledge base, or FALSE if you cannot.
"""

import os.path
import collections
import itertools
import copy

# declare global variable
gCounter = 0

# creates combinations of variables for standardization
varArray = list("abcdefghijklmnopqrstuvwxyz")
varArray2 = []
varArray3 = []
for eachComb in itertools.permutations(varArray, 2):
    varArray2.append(eachComb[0] + eachComb[1])
for eachComb in itertools.permutations(varArray, 3):
    varArray3.append(eachComb[0] + eachComb[1] + eachComb[2])
varArray = varArray + varArray2 + varArray3
uppercaseArr = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


# Return the index at which an unmatched '(' occurs
def findOpenParenthesis(sentence):
    length = len(sentence)
    opens = []
    closes = []
    for i in range(length - 1, -1, -1):
        if sentence[i] == '(':
            opens.append(i)
        if sentence[i] == ')':
            closes.append(i)
        if len(opens) > len(closes):
            return opens[len(opens) - 1]
    return -1


# Return the index at which an unmatched ')' occurs
def findCloseParenthesis(sentence):
    length = len(sentence)
    opens = []
    closes = []

    for i in range(length):
        if sentence[i] == '(':
            opens.append(i)
        if sentence[i] == ')':
            closes.append(i)
        if len(closes) > len(opens):
            return closes[len(closes) - 1]
    return -1


# a => b is also (~a) | b
def eliminateImplies(startOfNegation, firstHalf, secondHalf):
    modifiedFH = firstHalf[:startOfNegation] + '(~' + firstHalf[startOfNegation:] + ')'
    s = modifiedFH + "|" + secondHalf
    return s


# a => b is also (~a) | b
def eliminateImpliesInSentence(sentence):
    countOfImplies = sentence.count('=>')
    for i in range(countOfImplies):
        index = sentence.find('=>')
        unmatchedOpenIndex = findOpenParenthesis(sentence[:index])
        sentence = eliminateImplies(unmatchedOpenIndex + 1, sentence[:index], sentence[index + 2:])
    return sentence


def negatePredicates(predicate1, operator, predicate2):
    # if predicate already contains negation, then remove negation else add negation
    if predicate1[0:2] == '(~':
        predicate1 = predicate1[2:len(predicate1) - 1]
    else:
        predicate1 = '(~' + predicate1 + ')'
    if predicate2[0:2] == '(~':
        predicate2 = predicate2[2:len(predicate2) - 1]
    else:
        predicate2 = '(~' + predicate2 + ')'

    sentence = predicate1 + operator + predicate2
    return sentence


# expand negation
def invertNegation(sentence):
    items = sentence.split('&')
    items = [item[2:len(item)-1] if item[1] == '~' else '(~'+item+')' for item in items]
    return '|'.join(items)


# This returns the position of '~' and where the predicate belonging to not ends
def findNegationPair(sentence, pattern):
    pairs = collections.OrderedDict()

    for i in range(len(sentence)):
        if i + 1 != len(sentence) and sentence[i] + sentence[i + 1] == pattern:
            pairs[i] = i + 2 + findCloseParenthesis(sentence[i + 2:])
    return pairs


# This returns the innermost pair of not from all possible pairs of notes
def getMostPatchPair(pairs, length):
    pairBegin = 0
    pairEnd = length
    for key, value in list(pairs.items()):
        if key > pairBegin and value < pairEnd:
            pairBegin = key
            pairEnd = value
    return [pairBegin, pairEnd]


# This function moves the negation in through the sentence
def negationExpand(sentence):
    while sentence.count('~(') != 0:
        pairs = findNegationPair(sentence, '~(')
        innermostPair = []
        if len(list(pairs.keys())) == 1:
            innermostPair = [list(pairs.keys())[0], pairs[list(pairs.keys())[0]]]
        else:
            innermostPair = getMostPatchPair(pairs, len(sentence))
        thirdPart = ""
        if innermostPair[1] + 1 != len(sentence):
            thirdPart = sentence[innermostPair[1] + 1:]
        sentence = sentence[:innermostPair[0]] + invertNegation(
            sentence[innermostPair[0]+2:innermostPair[1]]) + thirdPart
        negationExpand(sentence)
    return sentence


# (Take(x,y)) -> Take(x,y)
def removeParenthesisOfSingleItem(sentence):
    index = -1
    while index < len(sentence):
        indexOfOpen = sentence.find('(', index)
        if indexOfOpen != -1 and uppercaseArr.find(sentence[indexOfOpen + 1]) != -1:
            indeOfUnmatchedClose = findCloseParenthesis(sentence[indexOfOpen + 1:])
            sentenceAfterOpen = sentence[indexOfOpen + 1:indexOfOpen + indeOfUnmatchedClose + 1]
            if sentenceAfterOpen.count('(') == 1 and sentenceAfterOpen.count(')'):
                listSen = list(sentence)
                newSentence = ""
                for i, val in enumerate(listSen):
                    if i != indexOfOpen and i != indexOfOpen + 1 + indeOfUnmatchedClose:
                        newSentence += val
                sentence = newSentence
                index = 0
            else:
                index += 1
        else:
            index = index + 1
    return sentence


# (~Take(x,y)) -> ~Take(x,y)
def removeParenthesisOfSingleNegativeItem(sentence):
    index = 0
    while index < len(sentence):
        pairs = findNegationPair(sentence, '(~')
        if len(pairs) != 0:
            for pair in list(pairs.items()):
                eachKey = pair[0]
                eachVal = pair[1]
                sen = sentence[eachKey + 1:eachVal]
                if sen.count('(') == 1 and sen.count(')') == 1 and sen.count('&') == 0 and sen.count('|') == 0:
                    sentence = sentence[:eachKey] + sen + sentence[eachVal + 1:]
                    break
                else:
                    index += 1
        else:
            break
    return sentence


# if sentence contains ch, return its location(index)
def containsOf(sentence, ch):
    return [index for index, ltr in enumerate(sentence) if ltr == ch]


# returns indexes of '&' in sentence
def findIndexOfConjuncts(sentence):
    indexOfAnds = containsOf(sentence, '&')
    return indexOfAnds


# finds the two predicates around an '&'
def findOperandAroundConjuncts(sentence, index):
    predicate1 = sentence[:index]
    predicate2 = sentence[index + 1:]
    unmatchedOpen = findOpenParenthesis(predicate1)
    predicate1 = predicate1[unmatchedOpen + 1:]
    unmatchedClose = findCloseParenthesis(predicate2)
    predicate2 = predicate2[:unmatchedClose]
    return [predicate1, predicate2]


# finds the outermost '&' in a sentence
def findOutermostOfConjunction(sentence):
    list = []
    outermostIndex = -1
    for i in range(len(sentence)):
        if sentence[i] == '&' and len(list) == 1 and list[len(list) - 1] == '(':
            outermostIndex = i
            break
        elif sentence[i] == ')' and len(list) != 0:
            list.pop()
        elif sentence[i] == '(':
            list.append(sentence[i])
    return outermostIndex


# finds the outermost '|' in a sentence
def findOuterMostOr(sentence):
    list = []
    outermostIndex = -1
    for i in range(len(sentence)):
        if sentence[i] == '|' and len(list) == 1 and list[len(list) - 1] == '(':
            outermostIndex = i
            break
        elif sentence[i] == ')' and len(list) != 0:
            list.pop()
        elif sentence[i] == '(':
            list.append(sentence[i])
    return outermostIndex


# i.e) a | (b & c) = (a | b) & (a | c)  ii.e) (a & b) | c = (a | c) & (b | c)
def sentenceConjunction(sentence):
    type1 = conjunctionType1(sentence)
    type2 = conjunctionType2(type1)
    if type1 == type2:
        final = type1
    else:
        final = sentenceConjunction(type2)
    return final


# a | (b & c) = (a | b) & (a | c)
def conjunctionType1(sentence):
    index = 0
    while index < len(sentence):
        if sentence[index] == '|':
            leftSide = sentence[:index]
            rightSide = sentence[index + 1:]
            unmatchedOpen = findOpenParenthesis(sentence[:index])
            front = sentence[:unmatchedOpen + 1]
            orPredicate = sentence[unmatchedOpen + 1:index]
            unmatchedClose = findCloseParenthesis(rightSide)
            indexOfAnds = findIndexOfConjuncts(rightSide[:unmatchedClose])
            rear = rightSide[unmatchedClose:]
            if len(indexOfAnds) != 0:
                rightAndOperands = rightSide[:unmatchedClose]
                indexOfAnd = findOutermostOfConjunction(rightAndOperands)
                if indexOfAnd != -1:
                    andPredicates = findOperandAroundConjuncts(rightAndOperands, indexOfAnd)
                    distributedPredicates = '(' + orPredicate + '|' + andPredicates[0] + ')&(' + orPredicate + '|' + \
                                            andPredicates[1] + ')'
                    sentence = front + distributedPredicates + rear
                    index = 0
                else:
                    index += 1
            else:
                index += 1
        else:
            index += 1
    return sentence


# (a & b) | c = (a | c) & (b | c)
def conjunctionType2(sentence):
    index = 0
    while index < len(sentence):
        if sentence[index] == '|':
            leftSide = sentence[:index]
            rightSide = sentence[index + 1:]
            unmatchedClose = findCloseParenthesis(sentence[index + 1:])
            orPredicate = rightSide[:unmatchedClose]
            rear = rightSide[unmatchedClose:]
            unmatchedOpen = findOpenParenthesis(leftSide)
            front = sentence[:unmatchedOpen + 1]
            indexOfAnds = findIndexOfConjuncts(leftSide[unmatchedOpen + 1:])
            if len(indexOfAnds) != 0:
                leftAndOperands = leftSide[unmatchedOpen + 1:]
                indexOfAnd = findOutermostOfConjunction(leftAndOperands)
                if indexOfAnd != -1:
                    andPredicates = findOperandAroundConjuncts(leftAndOperands, indexOfAnd)
                    distributedPredicates = '(' + andPredicates[0] + '|' + orPredicate + ')&(' + andPredicates[
                        1] + '|' + orPredicate + ')'
                    sentence = front + distributedPredicates + rear
                    index = 0
                else:
                    index += 1
            else:
                index += 1
        else:
            index += 1
    return sentence


# (a | b) & c is split into a | b and c
def splitConjunction(sentence):
    index = findOutermostOfConjunction(sentence)
    if index == -1:
        kb1.append(sentence)
    else:
        left = sentence[:index]
        left1 = left[findOpenParenthesis(left) + 1:]
        right = sentence[index + 1:]
        right1 = right[:findCloseParenthesis(right)]
        splitConjunction(left1)
        splitConjunction(right1)


# ((a|b)|c) is just a|b|c
def cleanupParenthesis(sentence):
    i = 0
    value = ''
    while i < len(sentence):
        if sentence[i] == '|':
            left = sentence[:i]
            right = sentence[i:]
            indexOfUnmatchedOpen = findOpenParenthesis(left)
            if indexOfUnmatchedOpen == -1:
                i += 1
                continue
            indexOfUnmatchedClose = findCloseParenthesis(right) + len(left)
            value = ""
            for j, val in enumerate(sentence):
                if j != indexOfUnmatchedOpen and j != indexOfUnmatchedClose:
                    value = value + val
            sentence = value
        i += 1
    if value == '':
        kbWithoutParentheses.append(sentence)
    else:
        kbWithoutParentheses.append(value)


# finds all unique variables in a sentence
# variable is only a lower English letter
def getAllVariables(sentence):
    vars = set()
    varPositions = collections.OrderedDict()
    for i in range(len(sentence)):
        if (sentence[i - 1] == '(' or sentence[i - 1] == ',') and uppercaseArr.find(sentence[i]) == -1:
            vars.add(sentence[i])
            varPositions[i] = sentence[i]
    return [vars, varPositions]


# Standardize variables in a sentence
def normalizeVariable(args):
    global gCounter
    correspondingArgs = collections.OrderedDict()
    for eachArgument in args:
        correspondingArgs[eachArgument] = varArray[gCounter]
        gCounter = gCounter + 1
    return correspondingArgs


# finds the predicates in a sentence and creates a map of where the predicates occur in the kb according to line numbers
def findPredicate(sentence):
    predicateMap = collections.OrderedDict()
    i = 0
    start = 0
    while i != -1:
        i = sentence.find('(')
        if i != -1:
            predicate = sentence[start:i]
            sentence = sentence[i:]
            closeIndex = sentence.find(')')
            vars = sentence[1:closeIndex].split(",")
            if predicate not in list(predicateMap.keys()):
                predicateMap[predicate] = [vars]
            else:
                v = predicateMap[predicate]
                v.append(vars)
                predicateMap[predicate] = v
            i = sentence.find('|')
            if i != -1:
                i += 1
                sentence = sentence[i:len(sentence)]
    return predicateMap


# Checks if a value is a constant
def isConstant(str):
    if uppercaseArr.find(str[0]) != -1:
        return True
    else:
        return False


# finds a replacement for variable with another variable or constant
def replaceParam(paramArray, x, y):
    for index, eachVal in enumerate(paramArray):
        if eachVal == x:
            paramArray[index] = y
    return paramArray


# Unification
def unification(params1, params2):
    newParams = collections.OrderedDict()

    for i in range(len(params1)):
        if params1[i] != params2[i] and isConstant(params1[i]) and isConstant(params2[i]):
            return []
        elif params1[i] == params2[i] and isConstant(params1[i]) and isConstant(params2[i]):
            if params1[i] not in list(newParams.keys()):
                newParams[params1[i]] = params2[i]
        elif isConstant(params1[i]) and not isConstant(params2[i]):
            if params2[i] not in list(newParams.keys()):
                newParams[params2[i]] = params1[i]
                params2 = replaceParam(params2, params2[i], params1[i])
        elif not isConstant(params1[i]) and isConstant(params2[i]):
            if params1[i] not in list(newParams.keys()):
                newParams[params1[i]] = params2[i]
                params1 = replaceParam(params1, params1[i], params2[i])
        elif not isConstant(params1[i]) and not isConstant(params2[i]):
            if params1[i] not in list(newParams.keys()):
                newParams[params1[i]] = params2[i]
                params1 = replaceParam(params1, params1[i], params2[i])
    return newParams


# Checks if the sentence contradicts with any other sentence in kb
def checkForContradiction(newSentence, stdKb):
    if newSentence.count("(") == 1 and newSentence.count(")") == 1:
        negatedSentence = negateQuery(newSentence)
        for sen in stdKb:
            if sen == negatedSentence:
                newSentenceMap = collections.OrderedDict()
                newSentenceMap = findPredicate(newSentence)
                oldSentenceMap = collections.OrderedDict()
                oldSentenceMap = findPredicate(sen)
                answer1 = True
                answer2 = True
                for k, v in list(newSentenceMap.items()):
                    for val in v:
                        for val1 in val:
                            if not isConstant(val1):
                                answer1 = False
                                break
                for k, v in list(oldSentenceMap.items()):
                    for val in v:
                        for val1 in val:
                            if not isConstant(val1):
                                answer2 = False
                                break
                return answer1 | answer2
        return False
    else:
        return False


# negates a query to be added ot the kb and then perform resolution
def negateQuery(query):
    if query[0] == '~':
        query = query[1:]
    else:
        query = '~' + query
    return query


# checks if all params in a predicate are constants
def checkIfAllParamsAreConstants(params):
    areConstants = True
    for k, v in list(params.items()):
        if not isConstant(v):
            areConstants = False
            break
    return areConstants


if __name__ == '__main__':
    # input queries and kb
    instream = open("input.txt")
    lines = instream.readlines()
    queryCnt = int(lines[0].rstrip('\n'))
    queries = []
    for i in range(1, queryCnt + 1):
        queries.append(lines[i].rstrip('\n'))

    kbSentenceCnt = int(lines[queryCnt + 1])
    kb = []
    kb1 = []
    kbWithoutParentheses = []
    cleanKb = []

    for j in range(queryCnt + 2, queryCnt + kbSentenceCnt + 2):
        kbVal = (lines[j].rstrip('\n')).replace(" ", "")
        # parenthesis adding
        if len(kbVal.split('=>')) > 1:
            left = kbVal.split('=>')[0]
            right = kbVal.split('=>')[1]
            if right[0] == '~':
                right = '(' + right + ')'
            itemArr = left.split('&')
            itemArr = ['(' + item + ')' if item[0] == '~' else item for item in itemArr]
            left = '&'.join(itemArr)
            if len(itemArr) > 1:
                left = '(' + left + ')'
            kbVal = '(' + left + '=>' + right + ')'
        else:
            if kbVal[0] == '~':
                kbVal = '(' + kbVal + ')'

        if list(kbVal)[0] != '(' and list(kbVal)[0] != '~':# first letter is not open parenthesis and negation
            cleanKb.append(kbVal)
        elif kbVal.count('(') == 2 and kbVal.count('~') == 1:# open parenthesis - 2, negation - 1
            kbVal = kbVal[1:len(kbVal) - 1]
            cleanKb.append(kbVal)
        else:
            kb.append(kbVal)

    print("***** input file and construct KB *****")

    # create output file
    if os.path.isfile("output.txt"):
        outstream = open("output.txt", 'w')
        outstream.truncate()
    else:
        outstream = open("output.txt", 'w')

    # all sentence to CNF
    for knowledge in kb:
        knowledge = eliminateImpliesInSentence(knowledge)
        knowledge = negationExpand(knowledge)
        knowledge = removeParenthesisOfSingleNegativeItem(knowledge)
        knowledge = removeParenthesisOfSingleItem(knowledge)
        knowledge = sentenceConjunction(knowledge)
        splitConjunction(knowledge)
    print("***** successful to make CNF *****")
    for knowledge in kb1:
        cleanupParenthesis(knowledge)

    cleanKb = kbWithoutParentheses + cleanKb
    standardisedKb = []

    for knowledge in cleanKb:
        varsInSentence = getAllVariables(knowledge)
        vars = varsInSentence[0]
        correspondingVar = normalizeVariable(vars)
        varPositions = varsInSentence[1]
        listSen = list(knowledge)
        for eachPosition, eachVar in list(varPositions.items()):
            listSen[eachPosition] = correspondingVar[eachVar]
        standardisedKb.append("".join(listSen))

    kbMap = []
    allPredicates = collections.defaultdict(list)
    for index, eachSentence in enumerate(standardisedKb):
        sentenceMap = collections.OrderedDict()
        sentenceMap = findPredicate(eachSentence)
        for i in list(sentenceMap.keys()):
            allPredicates[i].append(index)
        kbMap.append(sentenceMap)

    for query in queries:
        workingPredicates = copy.deepcopy(allPredicates)
        result = False
        flagForBreak = 0
        normalizedKB = copy.deepcopy(standardisedKb)
        workingKBMap = copy.deepcopy(kbMap)
        query = query.replace(" ", "")
        negativeQuery = negateQuery(query)
        normalizedKB.append(negativeQuery)
        senMap = collections.OrderedDict()
        senMap = findPredicate(negativeQuery)
        workingKBMap.append(senMap)
        for iMap1 in list(senMap.keys()):
            workingPredicates[iMap1].append(len(workingKBMap) - 1)
        i = 0
        while i < len(workingKBMap) and i < 4000:
            j = 0
            if flagForBreak == 1:
                break
            sentenceMap1 = workingKBMap[i]
            for predicate1, parameters1 in list(sentenceMap1.items()):
                if flagForBreak == 1:
                    break
                for p1Index, p1 in enumerate(parameters1):
                    if flagForBreak == 1:
                        break
                    ll = len(workingPredicates[negateQuery(predicate1)])
                    while j < ll and ll < 100:
                        if flagForBreak == 1:
                            break
                        sentenceMap2 = workingKBMap[workingPredicates[negateQuery(predicate1)][j]]

                        for predicate2, parameters2 in list(sentenceMap2.items()):
                            if flagForBreak == 1:
                                break
                            for p2Index, p2 in enumerate(parameters2):
                                if predicate1 == negateQuery(predicate2) and sentenceMap1 != sentenceMap2:
                                    newParams = unification(copy.deepcopy(p1), copy.deepcopy(p2))
                                    if len(newParams) != 0:
                                        newSentence = ""
                                        for k, v in list(sentenceMap1.items()):
                                            for kIndex, value in enumerate(v):
                                                if k == predicate1 and p1Index == kIndex:
                                                    continue
                                                else:
                                                    newSentence += k + ' ( ' + " , ".join(value) + ' ) |'
                                        for k1, v1 in list(sentenceMap2.items()):
                                            for k1Index, value1 in enumerate(v1):
                                                if k1 == predicate2 and p2Index == k1Index:
                                                    continue
                                                else:
                                                    newSentence += k1 + ' ( ' + " , ".join(value1) + ' ) |'
                                        newSentence = newSentence[:len(newSentence) - 1]
                                        listSentence = newSentence.split()
                                        for k2, v2 in list(newParams.items()):
                                            for indexOfVal, val in enumerate(listSentence):
                                                if val == k2:
                                                    listSentence[indexOfVal] = v2
                                        newSentence = "".join(listSentence)
                                        if newSentence == "" and checkIfAllParamsAreConstants(newParams):
                                            result = True
                                        else:
                                            result = checkForContradiction(newSentence, normalizedKB)
                                        if result:
                                            flagForBreak = 1
                                            break
                                        else:
                                            if newSentence != "":
                                                noMatch = True
                                                newSentenceMap = collections.OrderedDict()
                                                newSentenceMap = findPredicate(newSentence)
                                                for eachMap in workingKBMap:
                                                    if eachMap == newSentenceMap:
                                                        noMatch = False
                                                        break
                                                if noMatch:
                                                    normalizedKB.append(newSentence)
                                                    workingKBMap.append(newSentenceMap)
                                                    for iMap in list(newSentenceMap.keys()):
                                                        workingPredicates[iMap].append(len(workingKBMap) - 1)
                        j = j + 1
            i = i + 1
        if result:
            output = 'TRUE'
        else:
            output = 'FALSE'
        outstream.write(output)
        outstream.write('\n')

    print("***** creating output.txt and write the inference result(s) into it *****")
    outstream.close()
