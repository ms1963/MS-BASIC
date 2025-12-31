package main

import (
	"bufio"
	"fmt"
	"io/ioutil"
	"math"
	"math/rand"
	"os"
	"os/signal"
	"sort"
	"strconv"
	"strings"
	"syscall"
	"time"
)

// VarType represents variable type
type VarType int

const (
	TypeSingle VarType = iota // Default floating point (!)
	TypeDouble                 // Double precision (#)
	TypeInteger                // Integer (%)
	TypeLong                   // Long integer (&)
	TypeString                 // String ($)
)

// LoopInfo stores information about a FOR loop
type LoopInfo struct {
	variable   string
	endValue   float64
	stepValue  float64
	startLine  int
	loopIndex  int
}

// WhileInfo stores information about a WHILE loop
type WhileInfo struct {
	startLine int
	loopIndex int
}

// FileHandle represents an open file
type FileHandle struct {
	scanner *bufio.Scanner
	writer  *bufio.Writer
	file    *os.File
	mode    string
	eof     bool
	lineNum int
}

// ErrorHandler stores error handling information
type ErrorHandler struct {
	enabled    bool
	lineNumber int
	lastError  int
	lastLine   int
}

// BasicInterpreter holds the interpreter state
type BasicInterpreter struct {
	variables      map[string]float64
	intVariables   map[string]int
	longVariables  map[string]int64
	dblVariables   map[string]float64
	stringVars     map[string]string
	arrays         map[string][]float64
	intArrays      map[string][]int
	longArrays     map[string][]int64
	dblArrays      map[string][]float64
	stringArrays   map[string][]string
	arrayDims      map[string][]int
	program        map[int]string
	running        bool
	programCounter int
	lineNumbers    []int
	loopStack      []LoopInfo
	whileStack     []WhileInfo
	inputScanner   *bufio.Scanner
	returnStack    []int
	dataValues     []string
	dataPointer    int
	rng            *rand.Rand
	memory         map[int]int
	files          map[int]*FileHandle
	nextFileNum    int
	optionBase     int
	defTypes       map[rune]VarType
	errorHandler   ErrorHandler
	startTime      time.Time
	cursorX        int
	cursorY        int
	currentFile    string
	interrupted    bool
}

// NewBasicInterpreter creates a new interpreter instance
func NewBasicInterpreter() *BasicInterpreter {
	return &BasicInterpreter{
		variables:    make(map[string]float64),
		intVariables: make(map[string]int),
		longVariables: make(map[string]int64),
		dblVariables: make(map[string]float64),
		stringVars:   make(map[string]string),
		arrays:       make(map[string][]float64),
		intArrays:    make(map[string][]int),
		longArrays:   make(map[string][]int64),
		dblArrays:    make(map[string][]float64),
		stringArrays: make(map[string][]string),
		arrayDims:    make(map[string][]int),
		program:      make(map[int]string),
		running:      false,
		lineNumbers:  []int{},
		loopStack:    []LoopInfo{},
		whileStack:   []WhileInfo{},
		inputScanner: bufio.NewScanner(os.Stdin),
		returnStack:  []int{},
		dataValues:   []string{},
		dataPointer:  0,
		rng:          rand.New(rand.NewSource(time.Now().UnixNano())),
		memory:       make(map[int]int),
		files:        make(map[int]*FileHandle),
		nextFileNum:  1,
		optionBase:   0,
		defTypes:     make(map[rune]VarType),
		errorHandler: ErrorHandler{enabled: false, lineNumber: 0, lastError: 0, lastLine: 0},
		startTime:    time.Now(),
		cursorX:      0,
		cursorY:      0,
		currentFile:  "",
		interrupted:  false,
	}
}

// getVarType returns the type of a variable based on its suffix or DEFTYPE
func (bi *BasicInterpreter) getVarType(name string) VarType {
	if len(name) == 0 {
		return TypeSingle
	}

	lastChar := name[len(name)-1]
	switch lastChar {
	case '$':
		return TypeString
	case '%':
		return TypeInteger
	case '&':
		return TypeLong
	case '#':
		return TypeDouble
	case '!':
		return TypeSingle
	}

	firstChar := rune(strings.ToUpper(name)[0])
	if varType, exists := bi.defTypes[firstChar]; exists {
		return varType
	}

	return TypeSingle
}

// Tokenize splits a line into tokens, preserving string literals
func (bi *BasicInterpreter) Tokenize(line string) []string {
	var tokens []string
	var current strings.Builder
	inString := false

	for i := 0; i < len(line); i++ {
		char := line[i]
		
		if char == '"' {
			inString = !inString
			current.WriteByte(char)
		} else if (char == ' ' || char == '\t') && !inString {
			if current.Len() > 0 {
				tokens = append(tokens, current.String())
				current.Reset()
			}
		} else if strings.ContainsRune("+-*/()=<>,;^$[]%#!&:\\", rune(char)) && !inString {
			if current.Len() > 0 {
				tokens = append(tokens, current.String())
				current.Reset()
			}
			if char == '<' && i+1 < len(line) {
				if line[i+1] == '>' || line[i+1] == '=' {
					tokens = append(tokens, string(line[i:i+2]))
					i++
					continue
				}
			}
			if char == '>' && i+1 < len(line) && line[i+1] == '=' {
				tokens = append(tokens, string(line[i:i+2]))
				i++
				continue
			}
			tokens = append(tokens, string(char))
		} else {
			current.WriteByte(char)
		}
	}

	if current.Len() > 0 {
		tokens = append(tokens, current.String())
	}

	return tokens
}

// isStringVar checks if a variable name is a string variable
func isStringVar(name string) bool {
	return len(name) > 0 && name[len(name)-1] == '$'
}

// isIntVar checks if a variable name is an integer variable
func isIntVar(name string) bool {
	return len(name) > 0 && name[len(name)-1] == '%'
}

// isLongVar checks if a variable name is a long variable
func isLongVar(name string) bool {
	return len(name) > 0 && name[len(name)-1] == '&'
}

// isDblVar checks if a variable name is a double variable
func isDblVar(name string) bool {
	return len(name) > 0 && name[len(name)-1] == '#'
}

// Expression parser using recursive descent
type ExprParser struct {
	tokens []string
	pos    int
	interp *BasicInterpreter
}

func (ep *ExprParser) peek() string {
	if ep.pos >= len(ep.tokens) {
		return ""
	}
	return ep.tokens[ep.pos]
}

func (ep *ExprParser) consume() string {
	token := ep.peek()
	ep.pos++
	return token
}

// ParseExpression is the entry point
func (ep *ExprParser) ParseExpression() (float64, error) {
	return ep.parseLogicalOr()
}

// parseLogicalOr handles OR, XOR, EQV, IMP
func (ep *ExprParser) parseLogicalOr() (float64, error) {
	left, err := ep.parseLogicalAnd()
	if err != nil {
		return 0, err
	}

	for {
		op := strings.ToUpper(ep.peek())
		if op != "OR" && op != "XOR" && op != "EQV" && op != "IMP" {
			break
		}
		ep.consume()

		right, err := ep.parseLogicalAnd()
		if err != nil {
			return 0, err
		}

		leftInt := int(left)
		rightInt := int(right)

		switch op {
		case "OR":
			left = float64(leftInt | rightInt)
		case "XOR":
			left = float64(leftInt ^ rightInt)
		case "EQV":
			left = float64(^(leftInt ^ rightInt))
		case "IMP":
			left = float64((^leftInt) | rightInt)
		}
	}

	return left, nil
}

// parseLogicalAnd handles AND
func (ep *ExprParser) parseLogicalAnd() (float64, error) {
	left, err := ep.parseLogicalNot()
	if err != nil {
		return 0, err
	}

	for strings.ToUpper(ep.peek()) == "AND" {
		ep.consume()
		right, err := ep.parseLogicalNot()
		if err != nil {
			return 0, err
		}

		leftInt := int(left)
		rightInt := int(right)
		left = float64(leftInt & rightInt)
	}

	return left, nil
}

// parseLogicalNot handles NOT
func (ep *ExprParser) parseLogicalNot() (float64, error) {
	if strings.ToUpper(ep.peek()) == "NOT" {
		ep.consume()
		val, err := ep.parseLogicalNot()
		if err != nil {
			return 0, err
		}
		return float64(^int(val)), nil
	}

	return ep.parseComparison()
}

// parseComparison handles comparison operators
func (ep *ExprParser) parseComparison() (float64, error) {
	left, err := ep.parseAddSub()
	if err != nil {
		return 0, err
	}

	op := ep.peek()
	if op == "=" || op == "<" || op == ">" || op == "<>" || op == "<=" || op == ">=" {
		ep.consume()

		right, err := ep.parseAddSub()
		if err != nil {
			return 0, err
		}

		var result bool
		switch op {
		case "=":
			result = left == right
		case "<":
			result = left < right
		case ">":
			result = left > right
		case "<=":
			result = left <= right
		case ">=":
			result = left >= right
		case "<>":
			result = left != right
		}

		if result {
			return -1, nil
		}
		return 0, nil
	}

	return left, nil
}

// parseAddSub handles addition and subtraction
func (ep *ExprParser) parseAddSub() (float64, error) {
	left, err := ep.parseTerm()
	if err != nil {
		return 0, err
	}

	for ep.peek() == "+" || ep.peek() == "-" {
		op := ep.consume()
		right, err := ep.parseTerm()
		if err != nil {
			return 0, err
		}

		if op == "+" {
			left = left + right
		} else {
			left = left - right
		}
	}

	return left, nil
}

// parseTerm handles multiplication and division
func (ep *ExprParser) parseTerm() (float64, error) {
	left, err := ep.parseIntDiv()
	if err != nil {
		return 0, err
	}

	for ep.peek() == "*" || ep.peek() == "/" {
		op := ep.consume()
		right, err := ep.parseIntDiv()
		if err != nil {
			return 0, err
		}

		if op == "*" {
			left = left * right
		} else {
			if right == 0 {
				return 0, fmt.Errorf("division by zero")
			}
			left = left / right
		}
	}

	return left, nil
}

// parseIntDiv handles integer division and MOD
func (ep *ExprParser) parseIntDiv() (float64, error) {
	left, err := ep.parsePower()
	if err != nil {
		return 0, err
	}

	for {
		op := ep.peek()
		opUpper := strings.ToUpper(op)
		if op != "\\" && opUpper != "MOD" {
			break
		}
		ep.consume()

		right, err := ep.parsePower()
		if err != nil {
			return 0, err
		}

		if right == 0 {
			return 0, fmt.Errorf("division by zero")
		}

		if op == "\\" {
			left = float64(int(left) / int(right))
		} else {
			left = float64(int(left) % int(right))
		}
	}

	return left, nil
}

// parsePower handles exponentiation
func (ep *ExprParser) parsePower() (float64, error) {
	left, err := ep.parseFactor()
	if err != nil {
		return 0, err
	}

	if ep.peek() == "^" {
		ep.consume()
		right, err := ep.parsePower()
		if err != nil {
			return 0, err
		}

		return math.Pow(left, right), nil
	}

	return left, nil
}

// parseFactor handles numbers, variables, arrays, functions, and parentheses
func (ep *ExprParser) parseFactor() (float64, error) {
	token := ep.peek()

	if token == "(" {
		ep.consume()
		result, err := ep.ParseExpression()
		if err != nil {
			return 0, err
		}
		if ep.peek() != ")" {
			return 0, fmt.Errorf("expected ')'")
		}
		ep.consume()
		return result, nil
	}

	if token == "-" {
		ep.consume()
		val, err := ep.parseFactor()
		if err != nil {
			return 0, err
		}
		return -val, nil
	}

	if token == "+" {
		ep.consume()
		return ep.parseFactor()
	}

	upperToken := strings.ToUpper(token)
	if ep.isFunction(upperToken) {
		return ep.parseFunction(upperToken)
	}

	ep.consume()

	if ep.peek() == "(" || ep.peek() == "[" {
		return ep.parseArrayAccess(token)
	}

	upperToken = strings.ToUpper(token)

	if isIntVar(upperToken) {
		if val, exists := ep.interp.intVariables[upperToken]; exists {
			return float64(val), nil
		}
		return 0, nil
	}

	if isLongVar(upperToken) {
		if val, exists := ep.interp.longVariables[upperToken]; exists {
			return float64(val), nil
		}
		return 0, nil
	}

	if isDblVar(upperToken) {
		if val, exists := ep.interp.dblVariables[upperToken]; exists {
			return val, nil
		}
		return 0, nil
	}

	if val, exists := ep.interp.variables[upperToken]; exists {
		return val, nil
	}

	if num, err := strconv.ParseFloat(token, 64); err == nil {
		return num, nil
	}

	if strings.HasPrefix(upperToken, "&H") {
		val, err := strconv.ParseInt(upperToken[2:], 16, 64)
		if err == nil {
			return float64(val), nil
		}
	} else if strings.HasPrefix(upperToken, "&O") {
		val, err := strconv.ParseInt(upperToken[2:], 8, 64)
		if err == nil {
			return float64(val), nil
		}
	} else if strings.HasPrefix(upperToken, "&") && len(upperToken) > 1 {
		val, err := strconv.ParseInt(upperToken[1:], 8, 64)
		if err == nil {
			return float64(val), nil
		}
	}

	return 0, nil
}

// parseArrayAccess handles array element access
func (ep *ExprParser) parseArrayAccess(arrayName string) (float64, error) {
	bracket := ep.consume()
	closeBracket := ")"
	if bracket == "[" {
		closeBracket = "]"
	}

	indexTokens := []string{}
	depth := 1
	for depth > 0 && ep.pos < len(ep.tokens) {
		t := ep.peek()
		if t == "(" || t == "[" {
			depth++
		} else if t == ")" || t == "]" {
			depth--
			if depth == 0 {
				break
			}
		}
		indexTokens = append(indexTokens, t)
		ep.consume()
	}

	if ep.peek() != closeBracket {
		return 0, fmt.Errorf("expected '%s'", closeBracket)
	}
	ep.consume()

	indexParser := &ExprParser{
		tokens: indexTokens,
		pos:    0,
		interp: ep.interp,
	}
	index, err := indexParser.ParseExpression()
	if err != nil {
		return 0, err
	}

	arrayName = strings.ToUpper(arrayName)
	idx := int(index) - ep.interp.optionBase

	if arr, exists := ep.interp.intArrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return 0, fmt.Errorf("array index out of bounds")
		}
		return float64(arr[idx]), nil
	}

	if arr, exists := ep.interp.longArrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return 0, fmt.Errorf("array index out of bounds")
		}
		return float64(arr[idx]), nil
	}

	if arr, exists := ep.interp.dblArrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return 0, fmt.Errorf("array index out of bounds")
		}
		return arr[idx], nil
	}

	if arr, exists := ep.interp.arrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return 0, fmt.Errorf("array index out of bounds")
		}
		return arr[idx], nil
	}

	return 0, fmt.Errorf("undefined array: %s", arrayName)
}

// isFunction checks if a token is a built-in function
func (ep *ExprParser) isFunction(token string) bool {
	functions := []string{
		"SQR", "ABS", "INT", "SIN", "COS", "TAN", "ATN", "ATN2", "EXP", "LOG",
		"RND", "SGN", "VAL", "ASC", "LEN", "PEEK", "FRE", "POS",
		"FIX", "CINT", "CLNG", "CSNG", "CDBL", "TIMER", "ERR", "ERL",
		"LBOUND", "UBOUND", "EOF", "INSTR", "LOF", "LOC",
	}
	for _, fn := range functions {
		if token == fn {
			return true
		}
	}
	return false
}

// parseFunction parses and evaluates a built-in function
func (ep *ExprParser) parseFunction(funcName string) (float64, error) {
	ep.consume()

	noParenFuncs := map[string]bool{
		"RND": true, "TIMER": true, "ERR": true, "ERL": true,
	}

	if noParenFuncs[funcName] && ep.peek() != "(" {
		switch funcName {
		case "RND":
			return ep.interp.rng.Float64(), nil
		case "TIMER":
			return time.Since(ep.interp.startTime).Seconds(), nil
		case "ERR":
			return float64(ep.interp.errorHandler.lastError), nil
		case "ERL":
			return float64(ep.interp.errorHandler.lastLine), nil
		}
	}

	if ep.peek() != "(" {
		return 0, fmt.Errorf("expected '(' after function %s", funcName)
	}
	ep.consume()

	argTokens := []string{}
	depth := 1
	for depth > 0 && ep.pos < len(ep.tokens) {
		t := ep.peek()
		if t == "(" {
			depth++
		} else if t == ")" {
			depth--
			if depth == 0 {
				break
			}
		}
		argTokens = append(argTokens, t)
		ep.consume()
	}

	if ep.peek() != ")" {
		return 0, fmt.Errorf("expected ')' after function arguments")
	}
	ep.consume()

	if funcName == "LEN" || funcName == "ASC" || funcName == "VAL" || funcName == "INSTR" {
		return ep.evaluateStringFunction(funcName, argTokens)
	}

	if funcName == "LBOUND" || funcName == "UBOUND" {
		return ep.evaluateArrayBounds(funcName, argTokens)
	}

	if funcName == "EOF" || funcName == "LOF" || funcName == "LOC" {
		return ep.evaluateFileFunction(funcName, argTokens)
	}

	if funcName == "PEEK" {
		addr, err := ep.interp.EvaluateExpression(argTokens)
		if err != nil {
			return 0, err
		}
		if val, exists := ep.interp.memory[int(addr)]; exists {
			return float64(val), nil
		}
		return 0, nil
	}

	if funcName == "FRE" {
		return 65536, nil
	}
	if funcName == "POS" {
		return float64(ep.interp.cursorX), nil
	}

	var arg float64
	var err error

	if len(argTokens) == 0 {
		arg = 0
	} else {
		argParser := &ExprParser{
			tokens: argTokens,
			pos:    0,
			interp: ep.interp,
		}
		arg, err = argParser.ParseExpression()
		if err != nil {
			return 0, err
		}
	}

	switch funcName {
	case "SQR":
		if arg < 0 {
			return 0, fmt.Errorf("SQR: negative argument")
		}
		return math.Sqrt(arg), nil
	case "ABS":
		return math.Abs(arg), nil
	case "INT":
		return math.Floor(arg), nil
	case "FIX":
		if arg >= 0 {
			return math.Floor(arg), nil
		}
		return math.Ceil(arg), nil
	case "CINT":
		return math.Round(arg), nil
	case "CLNG":
		return math.Round(arg), nil
	case "CSNG":
		return float64(float32(arg)), nil
	case "CDBL":
		return arg, nil
	case "SIN":
		return math.Sin(arg), nil
	case "COS":
		return math.Cos(arg), nil
	case "TAN":
		return math.Tan(arg), nil
	case "ATN":
		return math.Atan(arg), nil
	case "EXP":
		return math.Exp(arg), nil
	case "LOG":
		if arg <= 0 {
			return 0, fmt.Errorf("LOG: non-positive argument")
		}
		return math.Log(arg), nil
	case "RND":
		if arg < 0 {
			ep.interp.rng = rand.New(rand.NewSource(int64(arg * 1000000)))
		}
		return ep.interp.rng.Float64(), nil
	case "SGN":
		if arg < 0 {
			return -1, nil
		} else if arg > 0 {
			return 1, nil
		}
		return 0, nil
	case "TIMER":
		return time.Since(ep.interp.startTime).Seconds(), nil
	case "ERR":
		return float64(ep.interp.errorHandler.lastError), nil
	case "ERL":
		return float64(ep.interp.errorHandler.lastLine), nil
	default:
		return 0, fmt.Errorf("unknown function: %s", funcName)
	}
}

// evaluateStringFunction evaluates string functions that return numbers
func (ep *ExprParser) evaluateStringFunction(funcName string, argTokens []string) (float64, error) {
	switch funcName {
	case "LEN":
		str, err := ep.interp.EvaluateStringExpression(argTokens)
		if err != nil {
			return 0, err
		}
		return float64(len(str)), nil

	case "ASC":
		str, err := ep.interp.EvaluateStringExpression(argTokens)
		if err != nil {
			return 0, err
		}
		if len(str) == 0 {
			return 0, fmt.Errorf("ASC: empty string")
		}
		return float64(str[0]), nil

	case "VAL":
		str, err := ep.interp.EvaluateStringExpression(argTokens)
		if err != nil {
			return 0, err
		}
		val, err := strconv.ParseFloat(strings.TrimSpace(str), 64)
		if err != nil {
			return 0, nil
		}
		return val, nil

	case "INSTR":
		return ep.evaluateInstr(argTokens)

	default:
		return 0, fmt.Errorf("unknown string function: %s", funcName)
	}
}

// evaluateInstr evaluates INSTR function
func (ep *ExprParser) evaluateInstr(argTokens []string) (float64, error) {
	commas := []int{}
	depth := 0
	for i, token := range argTokens {
		if token == "(" {
			depth++
		} else if token == ")" {
			depth--
		} else if token == "," && depth == 0 {
			commas = append(commas, i)
		}
	}

	var start int = 1
	var str1Tokens, str2Tokens []string

	if len(commas) == 1 {
		str1Tokens = argTokens[:commas[0]]
		str2Tokens = argTokens[commas[0]+1:]
	} else if len(commas) == 2 {
		startTokens := argTokens[:commas[0]]
		startVal, err := ep.interp.EvaluateExpression(startTokens)
		if err != nil {
			return 0, err
		}
		start = int(startVal)
		str1Tokens = argTokens[commas[0]+1 : commas[1]]
		str2Tokens = argTokens[commas[1]+1:]
	} else {
		return 0, fmt.Errorf("INSTR requires 2 or 3 arguments")
	}

	str1, err := ep.interp.EvaluateStringExpression(str1Tokens)
	if err != nil {
		return 0, err
	}
	str2, err := ep.interp.EvaluateStringExpression(str2Tokens)
	if err != nil {
		return 0, err
	}

	if start < 1 || start > len(str1) {
		return 0, nil
	}

	pos := strings.Index(str1[start-1:], str2)
	if pos == -1 {
		return 0, nil
	}
	return float64(pos + start), nil
}

// evaluateArrayBounds evaluates LBOUND and UBOUND
func (ep *ExprParser) evaluateArrayBounds(funcName string, argTokens []string) (float64, error) {
	if len(argTokens) == 0 {
		return 0, fmt.Errorf("%s requires array name", funcName)
	}

	arrayName := strings.ToUpper(argTokens[0])

	if funcName == "LBOUND" {
		return float64(ep.interp.optionBase), nil
	}

	if dims, exists := ep.interp.arrayDims[arrayName]; exists {
		if len(dims) > 0 {
			return float64(dims[0] - 1 + ep.interp.optionBase), nil
		}
	}

	return 0, fmt.Errorf("array not found: %s", arrayName)
}

// evaluateFileFunction evaluates file-related functions
func (ep *ExprParser) evaluateFileFunction(funcName string, argTokens []string) (float64, error) {
	fileNum, err := ep.interp.EvaluateExpression(argTokens)
	if err != nil {
		return 0, err
	}

	fh, exists := ep.interp.files[int(fileNum)]
	if !exists {
		return -1, nil
	}

	switch funcName {
	case "EOF":
		if fh.eof {
			return -1, nil
		}
		return 0, nil
	case "LOF":
		if fh.file != nil {
			info, err := fh.file.Stat()
			if err == nil {
				return float64(info.Size()), nil
			}
		}
		return 0, nil
	case "LOC":
		return float64(fh.lineNum), nil
	}

	return 0, nil
}

// EvaluateExpression evaluates an arithmetic expression
func (bi *BasicInterpreter) EvaluateExpression(tokens []string) (float64, error) {
	if len(tokens) == 0 {
		return 0, fmt.Errorf("empty expression")
	}

	parser := &ExprParser{
		tokens: tokens,
		pos:    0,
		interp: bi,
	}

	result, err := parser.ParseExpression()
	if err != nil {
		return 0, err
	}

	if parser.pos < len(tokens) {
		return 0, fmt.Errorf("unexpected token: %s", tokens[parser.pos])
	}

	return result, nil
}

// EvaluateStringExpression evaluates a string expression
func (bi *BasicInterpreter) EvaluateStringExpression(tokens []string) (string, error) {
	if len(tokens) == 0 {
		return "", fmt.Errorf("empty expression")
	}

	if len(tokens) > 0 {
		upperToken := strings.ToUpper(tokens[0])
		stringFuncs := []string{
			"LEFT$", "RIGHT$", "MID$", "CHR$", "STR$", "STRING$",
			"SPACE$", "HEX$", "OCT$", "LCASE$", "UCASE$",
			"TIME$", "DATE$", "INPUT$",
		}
		for _, fn := range stringFuncs {
			if upperToken == fn {
				return bi.evaluateStringFunction(tokens)
			}
		}
	}

	if len(tokens) == 1 && strings.HasPrefix(tokens[0], `"`) && strings.HasSuffix(tokens[0], `"`) {
		return tokens[0][1 : len(tokens[0])-1], nil
	}

	if len(tokens) == 1 && isStringVar(tokens[0]) {
		varName := strings.ToUpper(tokens[0])
		if val, exists := bi.stringVars[varName]; exists {
			return val, nil
		}
		return "", nil
	}

	if len(tokens) >= 3 && (tokens[1] == "(" || tokens[1] == "[") {
		return bi.getStringArrayElement(tokens)
	}

	result := ""
	i := 0
	for i < len(tokens) {
		if tokens[i] == "+" {
			i++
			continue
		}

		if strings.HasPrefix(tokens[i], `"`) && strings.HasSuffix(tokens[i], `"`) {
			result += tokens[i][1 : len(tokens[i])-1]
		} else if isStringVar(tokens[i]) {
			varName := strings.ToUpper(tokens[i])
			if val, exists := bi.stringVars[varName]; exists {
				result += val
			}
		} else {
			return "", fmt.Errorf("invalid string expression")
		}
		i++
	}

	return result, nil
}

// getStringArrayElement retrieves a string array element
func (bi *BasicInterpreter) getStringArrayElement(tokens []string) (string, error) {
	arrayName := strings.ToUpper(tokens[0])

	indexTokens := []string{}
	i := 2
	depth := 1
	for i < len(tokens) && depth > 0 {
		if tokens[i] == "(" || tokens[i] == "[" {
			depth++
		} else if tokens[i] == ")" || tokens[i] == "]" {
			depth--
			if depth == 0 {
				break
			}
		}
		indexTokens = append(indexTokens, tokens[i])
		i++
	}

	index, err := bi.EvaluateExpression(indexTokens)
	if err != nil {
		return "", err
	}

	idx := int(index) - bi.optionBase
	if arr, exists := bi.stringArrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return "", fmt.Errorf("array index out of bounds")
		}
		return arr[idx], nil
	}

	return "", fmt.Errorf("undefined string array: %s", arrayName)
}

// evaluateStringFunction evaluates string functions
func (bi *BasicInterpreter) evaluateStringFunction(tokens []string) (string, error) {
	funcName := strings.ToUpper(tokens[0])

	if funcName == "TIME$" && len(tokens) == 1 {
		return time.Now().Format("15:04:05"), nil
	}
	if funcName == "DATE$" && len(tokens) == 1 {
		return time.Now().Format("01-02-2006"), nil
	}

	if len(tokens) < 2 || tokens[1] != "(" {
		return "", fmt.Errorf("expected '(' after %s", funcName)
	}

	depth := 1
	argStart := 2
	argEnd := argStart
	for argEnd < len(tokens) && depth > 0 {
		if tokens[argEnd] == "(" {
			depth++
		} else if tokens[argEnd] == ")" {
			depth--
		}
		if depth > 0 {
			argEnd++
		}
	}

	if depth != 0 {
		return "", fmt.Errorf("unmatched parentheses in %s", funcName)
	}

	argTokens := tokens[argStart:argEnd]

	switch funcName {
	case "CHR$":
		val, err := bi.EvaluateExpression(argTokens)
		if err != nil {
			return "", err
		}
		return string(rune(int(val))), nil

	case "STR$":
		val, err := bi.EvaluateExpression(argTokens)
		if err != nil {
			return "", err
		}
		if val == float64(int(val)) {
			if val >= 0 {
				return fmt.Sprintf(" %d", int(val)), nil
			}
			return fmt.Sprintf("%d", int(val)), nil
		}
		if val >= 0 {
			return fmt.Sprintf(" %g", val), nil
		}
		return fmt.Sprintf("%g", val), nil

	case "HEX$":
		val, err := bi.EvaluateExpression(argTokens)
		if err != nil {
			return "", err
		}
		return strings.ToUpper(fmt.Sprintf("%X", int(val))), nil

	case "OCT$":
		val, err := bi.EvaluateExpression(argTokens)
		if err != nil {
			return "", err
		}
		return fmt.Sprintf("%o", int(val)), nil

	case "SPACE$":
		val, err := bi.EvaluateExpression(argTokens)
		if err != nil {
			return "", err
		}
		return strings.Repeat(" ", int(val)), nil

	case "STRING$":
		return bi.evaluateStringDollar(argTokens)

	case "LEFT$":
		return bi.evaluateLeftRight(argTokens, true)

	case "RIGHT$":
		return bi.evaluateLeftRight(argTokens, false)

	case "MID$":
		return bi.evaluateMid(argTokens)

	case "LCASE$":
		str, err := bi.EvaluateStringExpression(argTokens)
		if err != nil {
			return "", err
		}
		return strings.ToLower(str), nil

	case "UCASE$":
		str, err := bi.EvaluateStringExpression(argTokens)
		if err != nil {
			return "", err
		}
		return strings.ToUpper(str), nil

	case "TIME$":
		return time.Now().Format("15:04:05"), nil

	case "DATE$":
		return time.Now().Format("01-02-2006"), nil

	case "INPUT$":
		commas := []int{}
		depth := 0
		for i, token := range argTokens {
			if token == "(" {
				depth++
			} else if token == ")" {
				depth--
			} else if token == "," && depth == 0 {
				commas = append(commas, i)
			}
		}

		if len(commas) == 0 {
			countVal, err := bi.EvaluateExpression(argTokens)
			if err != nil {
				return "", err
			}
			result := ""
			for i := 0; i < int(countVal); i++ {
				var b [1]byte
				os.Stdin.Read(b[:])
				result += string(b[0])
			}
			return result, nil
		} else {
			countTokens := argTokens[:commas[0]]
			countVal, err := bi.EvaluateExpression(countTokens)
			if err != nil {
				return "", err
			}

			fileTokens := argTokens[commas[0]+1:]
			if len(fileTokens) > 0 && fileTokens[0] == "#" {
				fileTokens = fileTokens[1:]
			}

			fileNum, err := bi.EvaluateExpression(fileTokens)
			if err != nil {
				return "", err
			}

			fh, exists := bi.files[int(fileNum)]
			if !exists {
				return "", fmt.Errorf("file not open")
			}

			result := make([]byte, int(countVal))
			n, _ := fh.file.Read(result)
			return string(result[:n]), nil
		}

	default:
		return "", fmt.Errorf("unknown string function: %s", funcName)
	}
}

// evaluateStringDollar handles STRING$ function
func (bi *BasicInterpreter) evaluateStringDollar(argTokens []string) (string, error) {
	commaIdx := -1
	depth := 0
	for i, token := range argTokens {
		if token == "(" {
			depth++
		} else if token == ")" {
			depth--
		} else if token == "," && depth == 0 {
			commaIdx = i
			break
		}
	}

	if commaIdx == -1 {
		return "", fmt.Errorf("STRING$ requires two arguments")
	}

	countTokens := argTokens[:commaIdx]
	count, err := bi.EvaluateExpression(countTokens)
	if err != nil {
		return "", err
	}

	charTokens := argTokens[commaIdx+1:]
	var char string

	if len(charTokens) == 1 && strings.HasPrefix(charTokens[0], `"`) && strings.HasSuffix(charTokens[0], `"`) {
		char = charTokens[0][1 : len(charTokens[0])-1]
		if len(char) > 0 {
			char = string(char[0])
		}
	} else {
		charCode, err := bi.EvaluateExpression(charTokens)
		if err != nil {
			return "", err
		}
		char = string(rune(int(charCode)))
	}

	return strings.Repeat(char, int(count)), nil
}

// evaluateLeftRight handles LEFT$ and RIGHT$
func (bi *BasicInterpreter) evaluateLeftRight(argTokens []string, isLeft bool) (string, error) {
	commaIdx := -1
	depth := 0
	for i, token := range argTokens {
		if token == "(" {
			depth++
		} else if token == ")" {
			depth--
		} else if token == "," && depth == 0 {
			commaIdx = i
			break
		}
	}

	if commaIdx == -1 {
		return "", fmt.Errorf("LEFT$/RIGHT$ requires two arguments")
	}

	strTokens := argTokens[:commaIdx]
	str, err := bi.EvaluateStringExpression(strTokens)
	if err != nil {
		return "", err
	}

	lenTokens := argTokens[commaIdx+1:]
	length, err := bi.EvaluateExpression(lenTokens)
	if err != nil {
		return "", err
	}

	n := int(length)
	if n < 0 {
		n = 0
	}
	if n > len(str) {
		n = len(str)
	}

	if isLeft {
		return str[:n], nil
	}
	return str[len(str)-n:], nil
}

// evaluateMid handles MID$
func (bi *BasicInterpreter) evaluateMid(argTokens []string) (string, error) {
	commas := []int{}
	depth := 0
	for i, token := range argTokens {
		if token == "(" {
			depth++
		} else if token == ")" {
			depth--
		} else if token == "," && depth == 0 {
			commas = append(commas, i)
		}
	}

	if len(commas) < 1 {
		return "", fmt.Errorf("MID$ requires at least two arguments")
	}

	strTokens := argTokens[:commas[0]]
	str, err := bi.EvaluateStringExpression(strTokens)
	if err != nil {
		return "", err
	}

	var startTokens []string
	if len(commas) == 1 {
		startTokens = argTokens[commas[0]+1:]
	} else {
		startTokens = argTokens[commas[0]+1 : commas[1]]
	}

	start, err := bi.EvaluateExpression(startTokens)
	if err != nil {
		return "", err
	}

	startPos := int(start) - 1
	if startPos < 0 {
		startPos = 0
	}
	if startPos >= len(str) {
		return "", nil
	}

	if len(commas) >= 2 {
		lenTokens := argTokens[commas[1]+1:]
		length, err := bi.EvaluateExpression(lenTokens)
		if err != nil {
			return "", err
		}

		n := int(length)
		endPos := startPos + n
		if endPos > len(str) {
			endPos = len(str)
		}
		return str[startPos:endPos], nil
	}

	return str[startPos:], nil
}

// EvaluateCondition evaluates a conditional expression
func (bi *BasicInterpreter) EvaluateCondition(tokens []string) (bool, error) {
	result, err := bi.EvaluateExpression(tokens)
	if err != nil {
		return false, err
	}

	return result != 0, nil
}

// ExecuteLine executes a single line of BASIC code
func (bi *BasicInterpreter) ExecuteLine(line string) error {
	line = strings.TrimSpace(line)
	if line == "" {
		return nil
	}

	tokens := bi.Tokenize(line)
	if len(tokens) > 0 {
		if lineNum, err := strconv.Atoi(tokens[0]); err == nil {
			if len(tokens) == 1 {
				delete(bi.program, lineNum)
			} else {
				restOfLine := strings.TrimSpace(line[len(tokens[0]):])
				bi.program[lineNum] = restOfLine
			}
			return nil
		}
	}

	return bi.executeStatement(line)
}

// executeStatement executes a BASIC statement
func (bi *BasicInterpreter) executeStatement(line string) error {
	defer func() {
		if r := recover(); r != nil {
			if bi.errorHandler.enabled && bi.running {
				bi.errorHandler.lastError = 1
				if bi.programCounter >= 0 && bi.programCounter < len(bi.lineNumbers) {
					bi.errorHandler.lastLine = bi.lineNumbers[bi.programCounter]
				}
				for i, lineNum := range bi.lineNumbers {
					if lineNum == bi.errorHandler.lineNumber {
						bi.programCounter = i - 1
						return
					}
				}
			}
		}
	}()

	trimmed := strings.TrimSpace(line)
	if strings.HasPrefix(strings.ToUpper(trimmed), "REM") || strings.HasPrefix(trimmed, "'") {
		return nil
	}

	originalLine := line
	tokens := bi.Tokenize(strings.ToUpper(line))
	if len(tokens) == 0 {
		return nil
	}

	switch tokens[0] {
	case "RUN":
		return bi.runProgram()
	case "LIST":
		return bi.listProgram()
	case "NEW":
		return bi.newProgram()
	case "LOAD":
		return bi.executeLoad(tokens[1:], originalLine)
	case "SAVE":
		return bi.executeSave(tokens[1:], originalLine)
	case "FILES":
		return bi.executeFiles()
	case "KILL":
		return bi.executeKill(tokens[1:], originalLine)
	case "NAME":
		return bi.executeName(tokens[1:], originalLine)
	case "PRINT", "?":
		return bi.executePrint(tokens[1:], originalLine)
	case "INPUT":
		return bi.executeInput(tokens[1:], originalLine)
	case "LINE":
		if len(tokens) > 1 && tokens[1] == "INPUT" {
			return bi.executeLineInput(tokens[2:], originalLine)
		}
		return fmt.Errorf("invalid LINE statement")
	case "DIM":
		return bi.executeDim(tokens[1:])
	case "GOTO":
		return bi.executeGoto(tokens[1:])
	case "GOSUB":
		return bi.executeGosub(tokens[1:])
	case "RETURN":
		return bi.executeReturn()
	case "ON":
		return bi.executeOn(tokens[1:])
	case "IF":
		return bi.executeIf(tokens[1:], originalLine)
	case "FOR":
		return bi.executeFor(tokens[1:])
	case "NEXT":
		return bi.executeNext(tokens[1:])
	case "WHILE":
		return bi.executeWhile(tokens[1:])
	case "WEND":
		return bi.executeWend()
	case "DATA":
		return bi.executeData(tokens[1:])
	case "READ":
		return bi.executeRead(tokens[1:])
	case "RESTORE":
		return bi.executeRestore()
	case "RANDOMIZE":
		if len(tokens) > 1 {
			seed, err := bi.EvaluateExpression(tokens[1:])
			if err != nil {
				return err
			}
			bi.rng = rand.New(rand.NewSource(int64(seed)))
		} else {
			bi.rng = rand.New(rand.NewSource(time.Now().UnixNano()))
		}
		return nil
	case "SWAP":
		return bi.executeSwap(tokens[1:])
	case "POKE":
		return bi.executePoke(tokens[1:])
	case "CLS":
		fmt.Print("\033[H\033[2J")
		bi.cursorX = 0
		bi.cursorY = 0
		return nil
	case "LOCATE":
		return bi.executeLocate(tokens[1:])
	case "COLOR":
		return bi.executeColor(tokens[1:])
	case "OPTION":
		return bi.executeOption(tokens[1:])
	case "DEFINT", "DEFSNG", "DEFDBL", "DEFSTR", "DEFLNG":
		return bi.executeDefType(tokens)
	case "ERASE":
		return bi.executeErase(tokens[1:])
	case "OPEN":
		return bi.executeOpen(tokens[1:], originalLine)
	case "CLOSE":
		return bi.executeClose(tokens[1:])
	case "WRITE":
		return bi.executeWrite(tokens[1:], originalLine)
	case "ERROR":
		return bi.executeError(tokens[1:])
	case "RESUME":
		return bi.executeResume(tokens[1:])
	case "REM", "'":
		return nil
	case "END", "STOP":
		if bi.running {
			bi.programCounter = len(bi.lineNumbers)
			if tokens[0] == "STOP" {
				fmt.Println("BREAK")
			}
		}
		return nil
	}

	if len(tokens) >= 3 {
		varIndex := 0
		if tokens[0] == "LET" {
			varIndex = 1
		}

		if varIndex+1 < len(tokens) && (tokens[varIndex+1] == "(" || tokens[varIndex+1] == "[") {
			return bi.executeArrayAssignment(tokens, varIndex, originalLine)
		}

		if varIndex < len(tokens)-2 && tokens[varIndex+1] == "=" {
			varName := tokens[varIndex]
			exprTokens := tokens[varIndex+2:]

			if isStringVar(varName) {
				origTokens := bi.Tokenize(originalLine)
				origExprStart := varIndex + 2
				if tokens[0] == "LET" {
					origExprStart++
				}
				if origExprStart < len(origTokens) {
					origExprTokens := origTokens[origExprStart:]
					value, err := bi.EvaluateStringExpression(origExprTokens)
					if err != nil {
						return err
					}
					bi.stringVars[varName] = value
					return nil
				}
			}

			value, err := bi.EvaluateExpression(exprTokens)
			if err != nil {
				return err
			}

			if isIntVar(varName) {
				bi.intVariables[varName] = int(value)
			} else if isLongVar(varName) {
				bi.longVariables[varName] = int64(value)
			} else if isDblVar(varName) {
				bi.dblVariables[varName] = value
			} else {
				bi.variables[varName] = value
			}
			return nil
		}
	}

	return fmt.Errorf("syntax error")
}

// executeLoad handles LOAD command
func (bi *BasicInterpreter) executeLoad(tokens []string, originalLine string) error {
	origTokens := bi.Tokenize(originalLine)
	
	loadIdx := -1
	for i, token := range origTokens {
		if strings.ToUpper(token) == "LOAD" {
			loadIdx = i
			break
		}
	}
	
	if loadIdx == -1 || loadIdx+1 >= len(origTokens) {
		return fmt.Errorf("LOAD requires a filename")
	}
	
	filename := origTokens[loadIdx+1]
	
	if strings.HasPrefix(filename, `"`) && strings.HasSuffix(filename, `"`) {
		filename = filename[1 : len(filename)-1]
	}
	
	if !strings.HasSuffix(strings.ToUpper(filename), ".BAS") {
		filename += ".BAS"
	}
	
	data, err := ioutil.ReadFile(filename)
	if err != nil {
		return fmt.Errorf("file not found: %s", filename)
	}
	
	bi.program = make(map[int]string)
	
	lines := strings.Split(string(data), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		
		tokens := bi.Tokenize(line)
		if len(tokens) > 0 {
			if lineNum, err := strconv.Atoi(tokens[0]); err == nil {
				if len(tokens) > 1 {
					restOfLine := strings.TrimSpace(line[len(tokens[0]):])
					bi.program[lineNum] = restOfLine
				}
			}
		}
	}
	
	bi.currentFile = filename
	fmt.Printf("Loaded: %s\n", filename)
	return nil
}

// executeSave handles SAVE command
func (bi *BasicInterpreter) executeSave(tokens []string, originalLine string) error {
	origTokens := bi.Tokenize(originalLine)
	
	saveIdx := -1
	for i, token := range origTokens {
		if strings.ToUpper(token) == "SAVE" {
			saveIdx = i
			break
		}
	}
	
	var filename string
	
	if saveIdx != -1 && saveIdx+1 < len(origTokens) {
		filename = origTokens[saveIdx+1]
		
		if strings.HasPrefix(filename, `"`) && strings.HasSuffix(filename, `"`) {
			filename = filename[1 : len(filename)-1]
		}
	} else if bi.currentFile != "" {
		filename = bi.currentFile
	} else {
		return fmt.Errorf("SAVE requires a filename")
	}
	
	if !strings.HasSuffix(strings.ToUpper(filename), ".BAS") {
		filename += ".BAS"
	}
	
	lineNumbers := make([]int, 0, len(bi.program))
	for lineNum := range bi.program {
		lineNumbers = append(lineNumbers, lineNum)
	}
	sort.Ints(lineNumbers)
	
	var programText strings.Builder
	for _, lineNum := range lineNumbers {
		programText.WriteString(fmt.Sprintf("%d %s\n", lineNum, bi.program[lineNum]))
	}
	
	err := ioutil.WriteFile(filename, []byte(programText.String()), 0644)
	if err != nil {
		return fmt.Errorf("error saving file: %v", err)
	}
	
	bi.currentFile = filename
	fmt.Printf("Saved: %s\n", filename)
	return nil
}

// executeFiles handles FILES command
func (bi *BasicInterpreter) executeFiles() error {
	files, err := ioutil.ReadDir(".")
	if err != nil {
		return fmt.Errorf("error reading directory: %v", err)
	}
	
	fmt.Println("\nBASIC Program Files:")
	fmt.Println("--------------------")
	
	count := 0
	for _, file := range files {
		if !file.IsDir() && strings.HasSuffix(strings.ToUpper(file.Name()), ".BAS") {
			fmt.Printf("%-20s %10d bytes\n", file.Name(), file.Size())
			count++
		}
	}
	
	if count == 0 {
		fmt.Println("No BASIC program files found.")
	} else {
		fmt.Printf("\n%d file(s)\n", count)
	}
	
	return nil
}

// executeKill handles KILL command
func (bi *BasicInterpreter) executeKill(tokens []string, originalLine string) error {
	origTokens := bi.Tokenize(originalLine)
	
	killIdx := -1
	for i, token := range origTokens {
		if strings.ToUpper(token) == "KILL" {
			killIdx = i
			break
		}
	}
	
	if killIdx == -1 || killIdx+1 >= len(origTokens) {
		return fmt.Errorf("KILL requires a filename")
	}
	
	filename := origTokens[killIdx+1]
	
	if strings.HasPrefix(filename, `"`) && strings.HasSuffix(filename, `"`) {
		filename = filename[1 : len(filename)-1]
	}
	
	err := os.Remove(filename)
	if err != nil {
		return fmt.Errorf("error deleting file: %v", err)
	}
	
	fmt.Printf("Deleted: %s\n", filename)
	return nil
}

// executeName handles NAME command
func (bi *BasicInterpreter) executeName(tokens []string, originalLine string) error {
	origTokens := bi.Tokenize(originalLine)
	
	nameIdx := -1
	asIdx := -1
	for i, token := range origTokens {
		if strings.ToUpper(token) == "NAME" {
			nameIdx = i
		}
		if strings.ToUpper(token) == "AS" {
			asIdx = i
		}
	}
	
	if nameIdx == -1 || asIdx == -1 || nameIdx+1 >= asIdx || asIdx+1 >= len(origTokens) {
		return fmt.Errorf("NAME requires: NAME oldfile AS newfile")
	}
	
	oldFile := origTokens[nameIdx+1]
	newFile := origTokens[asIdx+1]
	
	if strings.HasPrefix(oldFile, `"`) && strings.HasSuffix(oldFile, `"`) {
		oldFile = oldFile[1 : len(oldFile)-1]
	}
	if strings.HasPrefix(newFile, `"`) && strings.HasSuffix(newFile, `"`) {
		newFile = newFile[1 : len(newFile)-1]
	}
	
	err := os.Rename(oldFile, newFile)
	if err != nil {
		return fmt.Errorf("error renaming file: %v", err)
	}
	
	fmt.Printf("Renamed: %s to %s\n", oldFile, newFile)
	return nil
}

// executeLineInput handles LINE INPUT statement
func (bi *BasicInterpreter) executeLineInput(tokens []string, originalLine string) error {
	origTokens := bi.Tokenize(originalLine)
	
	startIdx := 0
	for i := 0; i < len(origTokens)-1; i++ {
		if strings.ToUpper(origTokens[i]) == "LINE" && strings.ToUpper(origTokens[i+1]) == "INPUT" {
			startIdx = i + 2
			break
		}
	}
	
	if startIdx >= len(origTokens) {
		return fmt.Errorf("LINE INPUT requires a variable")
	}
	
	origTokens = origTokens[startIdx:]
	if len(tokens) > len(origTokens) {
		tokens = tokens[len(tokens)-len(origTokens):]
	}
	
	prompt := ""
	varName := ""
	
	if len(origTokens) > 0 && strings.HasPrefix(origTokens[0], `"`) {
		promptEnd := -1
		for i, token := range origTokens {
			if strings.HasSuffix(token, `"`) {
				promptEnd = i
				break
			}
		}
		
		if promptEnd != -1 {
			for _, token := range origTokens[0 : promptEnd+1] {
				if strings.HasPrefix(token, `"`) {
					prompt += token[1:]
				} else if strings.HasSuffix(token, `"`) {
					prompt += token[:len(token)-1]
				} else {
					prompt += token
				}
				prompt += " "
			}
			prompt = strings.TrimSpace(prompt)
			
			if promptEnd+1 < len(tokens) && (tokens[promptEnd+1] == ";" || tokens[promptEnd+1] == ",") {
				if promptEnd+2 < len(tokens) {
					varName = tokens[promptEnd+2]
				}
			}
		}
	} else {
		if len(tokens) > 0 {
			varName = tokens[0]
		}
	}
	
	if varName == "" {
		return fmt.Errorf("LINE INPUT requires a variable")
	}
	
	if prompt != "" {
		fmt.Print(prompt)
	} else {
		fmt.Print("? ")
	}
	
	if !bi.inputScanner.Scan() {
		return fmt.Errorf("input error")
	}
	
	input := bi.inputScanner.Text()
	bi.stringVars[varName] = input
	
	return nil
}

// executeWhile handles WHILE statements
func (bi *BasicInterpreter) executeWhile(tokens []string) error {
	if !bi.running {
		return fmt.Errorf("WHILE only works in RUN mode")
	}

	condition, err := bi.EvaluateCondition(tokens)
	if err != nil {
		return err
	}

	if condition {
		whileInfo := WhileInfo{
			startLine: bi.lineNumbers[bi.programCounter],
			loopIndex: bi.programCounter,
		}
		bi.whileStack = append(bi.whileStack, whileInfo)
	} else {
		depth := 1
		for bi.programCounter+1 < len(bi.lineNumbers) {
			bi.programCounter++
			lineNum := bi.lineNumbers[bi.programCounter]
			code := bi.program[lineNum]
			upperCode := strings.ToUpper(strings.TrimSpace(code))

			if strings.HasPrefix(upperCode, "WHILE") {
				depth++
			} else if strings.HasPrefix(upperCode, "WEND") {
				depth--
				if depth == 0 {
					break
				}
			}
		}
	}

	return nil
}

// executeWend handles WEND statements
func (bi *BasicInterpreter) executeWend() error {
	if !bi.running {
		return fmt.Errorf("WEND only works in RUN mode")
	}

	if len(bi.whileStack) == 0 {
		return fmt.Errorf("WEND without WHILE")
	}

	whileInfo := bi.whileStack[len(bi.whileStack)-1]
	bi.whileStack = bi.whileStack[:len(bi.whileStack)-1]
	bi.programCounter = whileInfo.loopIndex - 1

	return nil
}

// executeOption handles OPTION BASE
func (bi *BasicInterpreter) executeOption(tokens []string) error {
	if len(tokens) < 2 || strings.ToUpper(tokens[0]) != "BASE" {
		return fmt.Errorf("invalid OPTION syntax")
	}

	base, err := strconv.Atoi(tokens[1])
	if err != nil || (base != 0 && base != 1) {
		return fmt.Errorf("OPTION BASE must be 0 or 1")
	}

	bi.optionBase = base
	return nil
}

// executeDefType handles DEFINT, DEFSNG, DEFDBL, DEFSTR, DEFLNG
func (bi *BasicInterpreter) executeDefType(tokens []string) error {
	if len(tokens) < 2 {
		return fmt.Errorf("invalid DEF syntax")
	}

	var varType VarType
	switch tokens[0] {
	case "DEFINT":
		varType = TypeInteger
	case "DEFLNG":
		varType = TypeLong
	case "DEFSNG":
		varType = TypeSingle
	case "DEFDBL":
		varType = TypeDouble
	case "DEFSTR":
		varType = TypeString
	}

	for i := 1; i < len(tokens); i++ {
		token := tokens[i]
		if token == "," {
			continue
		}

		if i+2 < len(tokens) && tokens[i+1] == "-" {
			start := rune(token[0])
			end := rune(tokens[i+2][0])
			for ch := start; ch <= end; ch++ {
				bi.defTypes[ch] = varType
			}
			i += 2
		} else {
			bi.defTypes[rune(token[0])] = varType
		}
	}

	return nil
}

// executeErase handles ERASE statement
func (bi *BasicInterpreter) executeErase(tokens []string) error {
	for _, token := range tokens {
		if token == "," {
			continue
		}
		arrayName := strings.ToUpper(token)
		delete(bi.arrays, arrayName)
		delete(bi.intArrays, arrayName)
		delete(bi.longArrays, arrayName)
		delete(bi.dblArrays, arrayName)
		delete(bi.stringArrays, arrayName)
		delete(bi.arrayDims, arrayName)
	}
	return nil
}

// executeLocate handles LOCATE statement
func (bi *BasicInterpreter) executeLocate(tokens []string) error {
	if len(tokens) < 1 {
		return nil
	}

	commaIdx := -1
	for i, token := range tokens {
		if token == "," {
			commaIdx = i
			break
		}
	}

	if commaIdx == -1 {
		row, err := bi.EvaluateExpression(tokens)
		if err != nil {
			return err
		}
		bi.cursorY = int(row)
	} else {
		rowTokens := tokens[:commaIdx]
		colTokens := tokens[commaIdx+1:]

		row, err := bi.EvaluateExpression(rowTokens)
		if err != nil {
			return err
		}
		col, err := bi.EvaluateExpression(colTokens)
		if err != nil {
			return err
		}

		bi.cursorY = int(row)
		bi.cursorX = int(col)
	}

	fmt.Printf("\033[%d;%dH", bi.cursorY, bi.cursorX)
	return nil
}

// executeColor handles COLOR statement
func (bi *BasicInterpreter) executeColor(tokens []string) error {
	return nil
}

// executeOpen handles OPEN statement
func (bi *BasicInterpreter) executeOpen(tokens []string, originalLine string) error {
	origTokens := bi.Tokenize(originalLine)

	startIdx := 0
	for i, token := range origTokens {
		if strings.ToUpper(token) == "OPEN" {
			startIdx = i + 1
			break
		}
	}
	origTokens = origTokens[startIdx:]

	if len(origTokens) < 5 {
		return fmt.Errorf("invalid OPEN syntax")
	}

	filename := ""
	if strings.HasPrefix(origTokens[0], `"`) && strings.HasSuffix(origTokens[0], `"`) {
		filename = origTokens[0][1 : len(origTokens[0])-1]
	} else {
		return fmt.Errorf("filename must be a string")
	}

	mode := ""
	fileNum := 0

	for i := 1; i < len(origTokens); i++ {
		upper := strings.ToUpper(origTokens[i])
		if upper == "FOR" && i+1 < len(origTokens) {
			mode = strings.ToUpper(origTokens[i+1])
		}
		if upper == "AS" && i+1 < len(origTokens) {
			numStr := origTokens[i+1]
			if strings.HasPrefix(numStr, "#") {
				numStr = numStr[1:]
			}
			num, err := strconv.Atoi(numStr)
			if err == nil {
				fileNum = num
			}
		}
	}

	if fileNum == 0 {
		fileNum = bi.nextFileNum
		bi.nextFileNum++
	}

	var file *os.File
	var err error
	var fh FileHandle

	switch mode {
	case "INPUT":
		file, err = os.Open(filename)
		if err != nil {
			return err
		}
		fh = FileHandle{
			scanner: bufio.NewScanner(file),
			file:    file,
			mode:    "INPUT",
			eof:     false,
			lineNum: 0,
		}
	case "OUTPUT":
		file, err = os.Create(filename)
		if err != nil {
			return err
		}
		fh = FileHandle{
			writer:  bufio.NewWriter(file),
			file:    file,
			mode:    "OUTPUT",
			eof:     false,
			lineNum: 0,
		}
	case "APPEND":
		file, err = os.OpenFile(filename, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
		if err != nil {
			return err
		}
		fh = FileHandle{
			writer:  bufio.NewWriter(file),
			file:    file,
			mode:    "APPEND",
			eof:     false,
			lineNum: 0,
		}
	default:
		return fmt.Errorf("invalid file mode: %s", mode)
	}

	bi.files[fileNum] = &fh
	return nil
}

// executeClose handles CLOSE statement
func (bi *BasicInterpreter) executeClose(tokens []string) error {
	if len(tokens) == 0 {
		for num, fh := range bi.files {
			if fh.writer != nil {
				fh.writer.Flush()
			}
			if fh.file != nil {
				fh.file.Close()
			}
			delete(bi.files, num)
		}
		return nil
	}

	for _, token := range tokens {
		if token == "," || token == "#" {
			continue
		}
		numStr := token
		if strings.HasPrefix(numStr, "#") {
			numStr = numStr[1:]
		}
		fileNum, err := strconv.Atoi(numStr)
		if err != nil {
			return err
		}

		if fh, exists := bi.files[fileNum]; exists {
			if fh.writer != nil {
				fh.writer.Flush()
			}
			if fh.file != nil {
				fh.file.Close()
			}
			delete(bi.files, fileNum)
		}
	}

	return nil
}

// executeWrite handles WRITE statement
func (bi *BasicInterpreter) executeWrite(tokens []string, originalLine string) error {
	if len(tokens) < 2 || tokens[0] != "#" {
		return fmt.Errorf("WRITE requires #filenum")
	}

	fileNum, err := strconv.Atoi(tokens[1])
	if err != nil {
		return err
	}

	fh, exists := bi.files[fileNum]
	if !exists {
		return fmt.Errorf("file not open")
	}

	if fh.mode != "OUTPUT" && fh.mode != "APPEND" {
		return fmt.Errorf("file not open for output")
	}

	if len(tokens) > 2 && tokens[2] == "," {
		dataTokens := tokens[3:]
		
		output := ""
		for i := 0; i < len(dataTokens); i++ {
			if dataTokens[i] == "," || dataTokens[i] == ";" {
				continue
			}
			
			if strings.HasPrefix(dataTokens[i], `"`) && strings.HasSuffix(dataTokens[i], `"`) {
				output += dataTokens[i][1:len(dataTokens[i])-1]
			} else if isStringVar(dataTokens[i]) {
				varName := strings.ToUpper(dataTokens[i])
				if val, exists := bi.stringVars[varName]; exists {
					output += `"` + val + `"`
				}
			} else {
				val, err := bi.EvaluateExpression([]string{dataTokens[i]})
				if err == nil {
					output += fmt.Sprintf("%g", val)
				}
			}
			
			if i < len(dataTokens)-1 {
				output += ","
			}
		}
		
		fh.writer.WriteString(output + "\n")
		fh.lineNum++
	}

	return nil
}

// executeError handles ON ERROR GOTO and ERROR statements
func (bi *BasicInterpreter) executeError(tokens []string) error {
	if len(tokens) >= 3 && strings.ToUpper(tokens[0]) == "ON" && strings.ToUpper(tokens[1]) == "ERROR" {
		if strings.ToUpper(tokens[2]) == "GOTO" {
			if len(tokens) > 3 {
				if tokens[3] == "0" {
					bi.errorHandler.enabled = false
					return nil
				}
				lineNum, err := strconv.Atoi(tokens[3])
				if err != nil {
					return err
				}
				bi.errorHandler.enabled = true
				bi.errorHandler.lineNumber = lineNum
				return nil
			}
		}
	}

	if len(tokens) > 0 {
		errNum, err := bi.EvaluateExpression(tokens)
		if err != nil {
			return err
		}
		bi.errorHandler.lastError = int(errNum)
		if bi.programCounter >= 0 && bi.programCounter < len(bi.lineNumbers) {
			bi.errorHandler.lastLine = bi.lineNumbers[bi.programCounter]
		}
		return fmt.Errorf("error %d", int(errNum))
	}

	return fmt.Errorf("invalid ERROR syntax")
}

// executeResume handles RESUME statement
func (bi *BasicInterpreter) executeResume(tokens []string) error {
	if !bi.running {
		return fmt.Errorf("RESUME only works in RUN mode")
	}

	if len(tokens) == 0 {
		for i, lineNum := range bi.lineNumbers {
			if lineNum == bi.errorHandler.lastLine {
				bi.programCounter = i - 1
				return nil
			}
		}
	} else if strings.ToUpper(tokens[0]) == "NEXT" {
		return nil
	} else {
		lineNum, err := strconv.Atoi(tokens[0])
		if err != nil {
			return err
		}
		for i, ln := range bi.lineNumbers {
			if ln == lineNum {
				bi.programCounter = i - 1
				return nil
			}
		}
	}

	return nil
}

// executeDim handles DIM statements
func (bi *BasicInterpreter) executeDim(tokens []string) error {
	if len(tokens) < 4 {
		return fmt.Errorf("invalid DIM syntax")
	}

	arrayName := tokens[0]
	varType := bi.getVarType(arrayName)

	if tokens[1] != "(" && tokens[1] != "[" {
		return fmt.Errorf("expected '(' or '[' after array name")
	}

	sizeTokens := []string{}
	for i := 2; i < len(tokens); i++ {
		if tokens[i] == ")" || tokens[i] == "]" {
			break
		}
		sizeTokens = append(sizeTokens, tokens[i])
	}

	size, err := bi.EvaluateExpression(sizeTokens)
	if err != nil {
		return err
	}

	arraySize := int(size) + 1 - bi.optionBase

	if arraySize < 0 {
		return fmt.Errorf("invalid array size")
	}

	bi.arrayDims[arrayName] = []int{int(size) + 1}

	switch varType {
	case TypeInteger:
		bi.intArrays[arrayName] = make([]int, arraySize)
	case TypeLong:
		bi.longArrays[arrayName] = make([]int64, arraySize)
	case TypeDouble:
		bi.dblArrays[arrayName] = make([]float64, arraySize)
	case TypeString:
		bi.stringArrays[arrayName] = make([]string, arraySize)
	default:
		bi.arrays[arrayName] = make([]float64, arraySize)
	}

	return nil
}

// executeArrayAssignment handles array element assignment
func (bi *BasicInterpreter) executeArrayAssignment(tokens []string, varIndex int, originalLine string) error {
	arrayName := tokens[varIndex]

	bracketStart := varIndex + 1
	if tokens[bracketStart] != "(" && tokens[bracketStart] != "[" {
		return fmt.Errorf("expected '(' or '[' after array name")
	}

	indexTokens := []string{}
	i := bracketStart + 1
	depth := 1
	for i < len(tokens) && depth > 0 {
		if tokens[i] == "(" || tokens[i] == "[" {
			depth++
		} else if tokens[i] == ")" || tokens[i] == "]" {
			depth--
			if depth == 0 {
				break
			}
		}
		indexTokens = append(indexTokens, tokens[i])
		i++
	}

	if i+1 >= len(tokens) || tokens[i+1] != "=" {
		return fmt.Errorf("expected '=' after array index")
	}

	valueTokens := tokens[i+2:]

	index, err := bi.EvaluateExpression(indexTokens)
	if err != nil {
		return err
	}

	idx := int(index) - bi.optionBase
	arrayName = strings.ToUpper(arrayName)

	if arr, exists := bi.stringArrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return fmt.Errorf("array index out of bounds")
		}

		origTokens := bi.Tokenize(originalLine)
		origValueStart := i + 2
		if tokens[0] == "LET" {
			origValueStart++
		}
		if origValueStart < len(origTokens) {
			origValueTokens := origTokens[origValueStart:]
			value, err := bi.EvaluateStringExpression(origValueTokens)
			if err != nil {
				return err
			}
			arr[idx] = value
		}
		return nil
	}

	value, err := bi.EvaluateExpression(valueTokens)
	if err != nil {
		return err
	}

	if arr, exists := bi.intArrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return fmt.Errorf("array index out of bounds")
		}
		arr[idx] = int(value)
		return nil
	}

	if arr, exists := bi.longArrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return fmt.Errorf("array index out of bounds")
		}
		arr[idx] = int64(value)
		return nil
	}

	if arr, exists := bi.dblArrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return fmt.Errorf("array index out of bounds")
		}
		arr[idx] = value
		return nil
	}

	if arr, exists := bi.arrays[arrayName]; exists {
		if idx < 0 || idx >= len(arr) {
			return fmt.Errorf("array index out of bounds")
		}
		arr[idx] = value
		return nil
	}

	return fmt.Errorf("undefined array: %s", arrayName)
}

// executeOn handles ON-GOTO and ON-GOSUB
func (bi *BasicInterpreter) executeOn(tokens []string) error {
	if len(tokens) < 3 {
		return fmt.Errorf("invalid ON syntax")
	}

	commandIdx := -1
	command := ""
	for i, token := range tokens {
		if token == "GOTO" || token == "GOSUB" {
			commandIdx = i
			command = token
			break
		}
		if token == "ERROR" {
			return bi.executeError(tokens)
		}
	}

	if commandIdx == -1 {
		return fmt.Errorf("ON requires GOTO or GOSUB")
	}

	exprTokens := tokens[:commandIdx]
	value, err := bi.EvaluateExpression(exprTokens)
	if err != nil {
		return err
	}

	index := int(value)
	if index < 1 {
		return nil
	}

	lineTokens := tokens[commandIdx+1:]
	lineNumbers := []string{}
	for _, token := range lineTokens {
		if token != "," {
			lineNumbers = append(lineNumbers, token)
		}
	}

	if index > len(lineNumbers) {
		return nil
	}

	targetLine := lineNumbers[index-1]

	if command == "GOTO" {
		return bi.executeGoto([]string{targetLine})
	}
	return bi.executeGosub([]string{targetLine})
}

// executeSwap handles SWAP statement
func (bi *BasicInterpreter) executeSwap(tokens []string) error {
	if len(tokens) != 3 || tokens[1] != "," {
		return fmt.Errorf("SWAP requires two variables separated by comma")
	}

	var1 := tokens[0]
	var2 := tokens[2]

	if isStringVar(var1) != isStringVar(var2) {
		return fmt.Errorf("SWAP: type mismatch")
	}

	if isStringVar(var1) {
		temp := bi.stringVars[var1]
		bi.stringVars[var1] = bi.stringVars[var2]
		bi.stringVars[var2] = temp
	} else if isIntVar(var1) {
		temp := bi.intVariables[var1]
		bi.intVariables[var1] = bi.intVariables[var2]
		bi.intVariables[var2] = temp
	} else if isLongVar(var1) {
		temp := bi.longVariables[var1]
		bi.longVariables[var1] = bi.longVariables[var2]
		bi.longVariables[var2] = temp
	} else {
		temp := bi.variables[var1]
		bi.variables[var1] = bi.variables[var2]
		bi.variables[var2] = temp
	}

	return nil
}

// executePoke handles POKE statement
func (bi *BasicInterpreter) executePoke(tokens []string) error {
	commaIdx := -1
	for i, token := range tokens {
		if token == "," {
			commaIdx = i
			break
		}
	}

	if commaIdx == -1 {
		return fmt.Errorf("POKE requires address and value")
	}

	addrTokens := tokens[:commaIdx]
	addr, err := bi.EvaluateExpression(addrTokens)
	if err != nil {
		return err
	}

	valTokens := tokens[commaIdx+1:]
	val, err := bi.EvaluateExpression(valTokens)
	if err != nil {
		return err
	}

	bi.memory[int(addr)] = int(val) & 0xFF
	return nil
}

// executeGosub handles GOSUB statements
func (bi *BasicInterpreter) executeGosub(tokens []string) error {
	if len(tokens) != 1 {
		return fmt.Errorf("GOSUB requires a line number")
	}

	targetLine, err := strconv.Atoi(tokens[0])
	if err != nil {
		return fmt.Errorf("invalid line number")
	}

	if !bi.running {
		return fmt.Errorf("GOSUB only works in RUN mode")
	}

	bi.returnStack = append(bi.returnStack, bi.programCounter)

	for i, lineNum := range bi.lineNumbers {
		if lineNum == targetLine {
			bi.programCounter = i - 1
			return nil
		}
	}

	return fmt.Errorf("line %d not found", targetLine)
}

// executeReturn handles RETURN statements
func (bi *BasicInterpreter) executeReturn() error {
	if !bi.running {
		return fmt.Errorf("RETURN only works in RUN mode")
	}

	if len(bi.returnStack) == 0 {
		return fmt.Errorf("RETURN without GOSUB")
	}

	returnAddr := bi.returnStack[len(bi.returnStack)-1]
	bi.returnStack = bi.returnStack[:len(bi.returnStack)-1]
	bi.programCounter = returnAddr

	return nil
}

// executeData handles DATA statements
func (bi *BasicInterpreter) executeData(tokens []string) error {
	return nil
}

// executeRead handles READ statements
func (bi *BasicInterpreter) executeRead(tokens []string) error {
	variables := []string{}
	for _, token := range tokens {
		if token != "," {
			variables = append(variables, token)
		}
	}

	if len(variables) == 0 {
		return fmt.Errorf("READ requires at least one variable")
	}

	for _, varName := range variables {
		if bi.dataPointer >= len(bi.dataValues) {
			return fmt.Errorf("out of DATA")
		}

		valueStr := bi.dataValues[bi.dataPointer]
		bi.dataPointer++

		if isStringVar(varName) {
			if strings.HasPrefix(valueStr, `"`) && strings.HasSuffix(valueStr, `"`) {
				valueStr = valueStr[1 : len(valueStr)-1]
			}
			bi.stringVars[varName] = valueStr
		} else {
			value, err := strconv.ParseFloat(valueStr, 64)
			if err != nil {
				return fmt.Errorf("invalid DATA value: %s", valueStr)
			}

			if isIntVar(varName) {
				bi.intVariables[varName] = int(value)
			} else if isLongVar(varName) {
				bi.longVariables[varName] = int64(value)
			} else if isDblVar(varName) {
				bi.dblVariables[varName] = value
			} else {
				bi.variables[varName] = value
			}
		}
	}

	return nil
}

// executeRestore handles RESTORE statements
func (bi *BasicInterpreter) executeRestore() error {
	bi.dataPointer = 0
	return nil
}

// collectDataValues collects all DATA values from the program
func (bi *BasicInterpreter) collectDataValues() {
	bi.dataValues = []string{}

	lineNumbers := make([]int, 0, len(bi.program))
	for lineNum := range bi.program {
		lineNumbers = append(lineNumbers, lineNum)
	}
	sort.Ints(lineNumbers)

	for _, lineNum := range lineNumbers {
		code := bi.program[lineNum]
		tokens := bi.Tokenize(code)

		if len(tokens) > 0 && strings.ToUpper(tokens[0]) == "DATA" {
			for i := 1; i < len(tokens); i++ {
				if tokens[i] != "," {
					bi.dataValues = append(bi.dataValues, tokens[i])
				}
			}
		}
	}
}

// executeInput handles INPUT statements
func (bi *BasicInterpreter) executeInput(tokens []string, originalLine string) error {
	if len(tokens) == 0 {
		return fmt.Errorf("INPUT requires a variable")
	}

	origTokens := bi.Tokenize(originalLine)
	
	inputIdx := -1
	for i, token := range origTokens {
		if strings.ToUpper(token) == "INPUT" {
			inputIdx = i
			break
		}
	}
	
	if inputIdx == -1 || inputIdx+1 >= len(origTokens) {
		return fmt.Errorf("INPUT requires a variable")
	}
	
	origTokens = origTokens[inputIdx+1:]
	if len(tokens) > len(origTokens) {
		tokens = tokens[len(tokens)-len(origTokens):]
	}

	prompt := ""
	varName := ""

	if len(origTokens) > 0 && strings.HasPrefix(origTokens[0], `"`) {
		promptEnd := -1
		for i, token := range origTokens {
			if strings.HasSuffix(token, `"`) {
				promptEnd = i
				break
			}
		}

		if promptEnd != -1 {
			for _, token := range origTokens[0 : promptEnd+1] {
				if strings.HasPrefix(token, `"`) {
					prompt += token[1:]
				} else if strings.HasSuffix(token, `"`) {
					prompt += token[:len(token)-1]
				} else {
					prompt += token
				}
				prompt += " "
			}
			prompt = strings.TrimSpace(prompt)

			if promptEnd+1 < len(tokens) && (tokens[promptEnd+1] == ";" || tokens[promptEnd+1] == ",") {
				if promptEnd+2 < len(tokens) {
					varName = tokens[promptEnd+2]
				}
			}
		}
	} else {
		if len(tokens) > 0 {
			varName = tokens[0]
		}
	}

	if varName == "" {
		return fmt.Errorf("INPUT requires a variable")
	}

	if prompt != "" {
		fmt.Print(prompt)
	} else {
		fmt.Print("? ")
	}

	if !bi.inputScanner.Scan() {
		return fmt.Errorf("input error")
	}

	input := strings.TrimSpace(bi.inputScanner.Text())

	if isStringVar(varName) {
		bi.stringVars[varName] = input
		return nil
	}

	value, err := strconv.ParseFloat(input, 64)
	if err != nil {
		return fmt.Errorf("invalid number: %s", input)
	}

	if isIntVar(varName) {
		bi.intVariables[varName] = int(value)
	} else if isLongVar(varName) {
		bi.longVariables[varName] = int64(value)
	} else if isDblVar(varName) {
		bi.dblVariables[varName] = value
	} else {
		bi.variables[varName] = value
	}

	return nil
}

// executeFor handles FOR statements
func (bi *BasicInterpreter) executeFor(tokens []string) error {
	if !bi.running {
		return fmt.Errorf("FOR only works in RUN mode")
	}

	if len(tokens) < 5 {
		return fmt.Errorf("invalid FOR syntax")
	}

	varName := tokens[0]
	if tokens[1] != "=" {
		return fmt.Errorf("expected '=' after variable in FOR")
	}

	toIndex := -1
	for i, token := range tokens {
		if token == "TO" {
			toIndex = i
			break
		}
	}

	if toIndex == -1 {
		return fmt.Errorf("FOR without TO")
	}

	startTokens := tokens[2:toIndex]
	startValue, err := bi.EvaluateExpression(startTokens)
	if err != nil {
		return err
	}

	stepIndex := -1
	for i := toIndex + 1; i < len(tokens); i++ {
		if tokens[i] == "STEP" {
			stepIndex = i
			break
		}
	}

	var endTokens []string
	if stepIndex == -1 {
		endTokens = tokens[toIndex+1:]
	} else {
		endTokens = tokens[toIndex+1 : stepIndex]
	}

	endValue, err := bi.EvaluateExpression(endTokens)
	if err != nil {
		return err
	}

	stepValue := 1.0
	if stepIndex != -1 {
		stepTokens := tokens[stepIndex+1:]
		stepValue, err = bi.EvaluateExpression(stepTokens)
		if err != nil {
			return err
		}
	}

	bi.variables[varName] = startValue

	loopInfo := LoopInfo{
		variable:  varName,
		endValue:  endValue,
		stepValue: stepValue,
		startLine: bi.lineNumbers[bi.programCounter],
		loopIndex: bi.programCounter,
	}
	bi.loopStack = append(bi.loopStack, loopInfo)

	return nil
}

// executeNext handles NEXT statements
func (bi *BasicInterpreter) executeNext(tokens []string) error {
	if !bi.running {
		return fmt.Errorf("NEXT only works in RUN mode")
	}

	if len(bi.loopStack) == 0 {
		return fmt.Errorf("NEXT without FOR")
	}

	loopInfo := bi.loopStack[len(bi.loopStack)-1]

	if len(tokens) > 0 && tokens[0] != loopInfo.variable {
		return fmt.Errorf("NEXT variable mismatch")
	}

	currentValue := bi.variables[loopInfo.variable]
	newValue := currentValue + loopInfo.stepValue
	bi.variables[loopInfo.variable] = newValue

	shouldContinue := false
	if loopInfo.stepValue > 0 {
		shouldContinue = newValue <= loopInfo.endValue
	} else {
		shouldContinue = newValue >= loopInfo.endValue
	}

	if shouldContinue {
		bi.programCounter = loopInfo.loopIndex
	} else {
		bi.loopStack = bi.loopStack[:len(bi.loopStack)-1]
	}

	return nil
}

// executeGoto handles GOTO statements
func (bi *BasicInterpreter) executeGoto(tokens []string) error {
	if len(tokens) != 1 {
		return fmt.Errorf("GOTO requires a line number")
	}

	targetLine, err := strconv.Atoi(tokens[0])
	if err != nil {
		return fmt.Errorf("invalid line number")
	}

	if !bi.running {
		return fmt.Errorf("GOTO only works in RUN mode")
	}

	for i, lineNum := range bi.lineNumbers {
		if lineNum == targetLine {
			bi.programCounter = i - 1
			return nil
		}
	}

	return fmt.Errorf("line %d not found", targetLine)
}

// executeIf handles IF-THEN-ELSE statements
func (bi *BasicInterpreter) executeIf(tokens []string, originalLine string) error {
	thenIndex := -1
	elseIndex := -1

	for i, token := range tokens {
		if token == "THEN" && thenIndex == -1 {
			thenIndex = i
		}
		if token == "ELSE" && elseIndex == -1 {
			elseIndex = i
		}
	}

	if thenIndex == -1 {
		return fmt.Errorf("IF without THEN")
	}

	conditionTokens := tokens[:thenIndex]
	condition, err := bi.EvaluateCondition(conditionTokens)
	if err != nil {
		return err
	}

	if condition {
		var thenTokens []string
		if elseIndex != -1 {
			thenTokens = tokens[thenIndex+1 : elseIndex]
		} else {
			thenTokens = tokens[thenIndex+1:]
		}

		if len(thenTokens) == 0 {
			return nil
		}

		if len(thenTokens) == 1 {
			if _, err := strconv.Atoi(thenTokens[0]); err == nil {
				return bi.executeGoto(thenTokens)
			}
		}

		origUpper := strings.ToUpper(originalLine)
		thenPos := strings.Index(origUpper, "THEN")
		if thenPos != -1 {
			var thenStatement string
			if elseIndex != -1 {
				elsePos := strings.Index(origUpper[thenPos:], "ELSE")
				if elsePos != -1 {
					thenStatement = strings.TrimSpace(originalLine[thenPos+4 : thenPos+elsePos])
				}
			} else {
				thenStatement = strings.TrimSpace(originalLine[thenPos+4:])
			}
			if thenStatement != "" {
				return bi.executeStatement(thenStatement)
			}
		}

		thenStatement := strings.Join(thenTokens, " ")
		return bi.executeStatement(thenStatement)
	} else if elseIndex != -1 {
		elseTokens := tokens[elseIndex+1:]

		if len(elseTokens) == 0 {
			return nil
		}

		if len(elseTokens) == 1 {
			if _, err := strconv.Atoi(elseTokens[0]); err == nil {
				return bi.executeGoto(elseTokens)
			}
		}

		origUpper := strings.ToUpper(originalLine)
		elsePos := strings.Index(origUpper, "ELSE")
		if elsePos != -1 {
			elseStatement := strings.TrimSpace(originalLine[elsePos+4:])
			if elseStatement != "" {
				return bi.executeStatement(elseStatement)
			}
		}

		elseStatement := strings.Join(elseTokens, " ")
		return bi.executeStatement(elseStatement)
	}

	return nil
}

// runProgram executes the stored program WITH CTRL+C SUPPORT
func (bi *BasicInterpreter) runProgram() error {
	if len(bi.program) == 0 {
		return fmt.Errorf("no program to run")
	}

	// Set up interrupt handler for Ctrl+C
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, os.Interrupt, syscall.SIGTERM)
	defer signal.Stop(sigChan)

	// Handle interrupts in a goroutine
	go func() {
		<-sigChan
		bi.interrupted = true
		fmt.Println("\n*** BREAK ***")
	}()

	// Reset state
	bi.variables = make(map[string]float64)
	bi.intVariables = make(map[string]int)
	bi.longVariables = make(map[string]int64)
	bi.dblVariables = make(map[string]float64)
	bi.stringVars = make(map[string]string)
	bi.arrays = make(map[string][]float64)
	bi.intArrays = make(map[string][]int)
	bi.longArrays = make(map[string][]int64)
	bi.dblArrays = make(map[string][]float64)
	bi.stringArrays = make(map[string][]string)
	bi.arrayDims = make(map[string][]int)
	bi.loopStack = []LoopInfo{}
	bi.whileStack = []WhileInfo{}
	bi.returnStack = []int{}
	bi.dataPointer = 0
	bi.interrupted = false
	bi.collectDataValues()
	bi.startTime = time.Now()

	bi.lineNumbers = make([]int, 0, len(bi.program))
	for lineNum := range bi.program {
		bi.lineNumbers = append(bi.lineNumbers, lineNum)
	}
	sort.Ints(bi.lineNumbers)

	bi.running = true
	bi.programCounter = 0

	for bi.programCounter < len(bi.lineNumbers) {
		// Check for Ctrl+C interrupt
		if bi.interrupted {
			bi.running = false
			bi.interrupted = false
			return nil
		}

		lineNum := bi.lineNumbers[bi.programCounter]
		code := bi.program[lineNum]

		if err := bi.executeStatement(code); err != nil {
			bi.running = false
			if !bi.errorHandler.enabled {
				return fmt.Errorf("error at line %d: %v", lineNum, err)
			}
		}

		bi.programCounter++
	}

	bi.running = false
	return nil
}

// listProgram displays the stored program
func (bi *BasicInterpreter) listProgram() error {
	if len(bi.program) == 0 {
		fmt.Println("No program in memory")
		return nil
	}

	lineNumbers := make([]int, 0, len(bi.program))
	for lineNum := range bi.program {
		lineNumbers = append(lineNumbers, lineNum)
	}
	sort.Ints(lineNumbers)

	for _, lineNum := range lineNumbers {
		fmt.Printf("%d %s\n", lineNum, bi.program[lineNum])
	}

	return nil
}

// newProgram clears the program and variables
func (bi *BasicInterpreter) newProgram() error {
	bi.program = make(map[int]string)
	bi.variables = make(map[string]float64)
	bi.intVariables = make(map[string]int)
	bi.longVariables = make(map[string]int64)
	bi.dblVariables = make(map[string]float64)
	bi.stringVars = make(map[string]string)
	bi.arrays = make(map[string][]float64)
	bi.intArrays = make(map[string][]int)
	bi.longArrays = make(map[string][]int64)
	bi.dblArrays = make(map[string][]float64)
	bi.stringArrays = make(map[string][]string)
	bi.arrayDims = make(map[string][]int)
	bi.lineNumbers = []int{}
	bi.loopStack = []LoopInfo{}
	bi.whileStack = []WhileInfo{}
	bi.returnStack = []int{}
	bi.dataValues = []string{}
	bi.dataPointer = 0
	bi.memory = make(map[int]int)
	
	for _, fh := range bi.files {
		if fh.writer != nil {
			fh.writer.Flush()
		}
		if fh.file != nil {
			fh.file.Close()
		}
	}
	bi.files = make(map[int]*FileHandle)
	bi.nextFileNum = 1
	
	bi.optionBase = 0
	bi.defTypes = make(map[rune]VarType)
	bi.errorHandler = ErrorHandler{enabled: false, lineNumber: 0, lastError: 0, lastLine: 0}
	bi.startTime = time.Now()
	bi.cursorX = 0
	bi.cursorY = 0
	bi.currentFile = ""
	bi.interrupted = false
	
	fmt.Println("Ready")
	return nil
}

// executePrint handles PRINT statements
func (bi *BasicInterpreter) executePrint(tokens []string, originalLine string) error {
	if len(tokens) == 0 {
		fmt.Println()
		return nil
	}

	origTokens := bi.Tokenize(originalLine)
	printIdx := -1
	for i, token := range origTokens {
		upper := strings.ToUpper(token)
		if upper == "PRINT" || upper == "?" {
			printIdx = i
			break
		}
	}
	if printIdx != -1 && printIdx+1 < len(origTokens) {
		origTokens = origTokens[printIdx+1:]
	} else {
		origTokens = tokens
	}

	output := ""
	currentExpr := []string{}
	currentOrigExpr := []string{}
	tokIdx := 0
	suppressNewline := false

	for i, token := range tokens {
		if token == ";" || token == "," {
			if len(currentExpr) > 0 {
				if len(currentOrigExpr) == 1 && strings.HasPrefix(currentOrigExpr[0], `"`) && strings.HasSuffix(currentOrigExpr[0], `"`) {
					output += currentOrigExpr[0][1 : len(currentOrigExpr[0])-1]
				} else if len(currentExpr) == 1 && isStringVar(currentExpr[0]) {
					varName := strings.ToUpper(currentExpr[0])
					if val, exists := bi.stringVars[varName]; exists {
						output += val
					}
				} else {
					value, err := bi.EvaluateExpression(currentExpr)
					if err != nil {
						return err
					}
					if value == float64(int(value)) {
						output += fmt.Sprintf(" %d", int(value))
					} else {
						output += fmt.Sprintf(" %g", value)
					}
				}
				currentExpr = []string{}
				currentOrigExpr = []string{}
			}

			if token == "," {
				tabPos := (len(output)/14 + 1) * 14
				output += strings.Repeat(" ", tabPos-len(output))
			}

			if i == len(tokens)-1 {
				suppressNewline = true
			}
		} else {
			currentExpr = append(currentExpr, token)
			if tokIdx < len(origTokens) {
				currentOrigExpr = append(currentOrigExpr, origTokens[tokIdx])
			}
		}
		tokIdx++

		if i == len(tokens)-1 && len(currentExpr) > 0 {
			if len(currentOrigExpr) == 1 && strings.HasPrefix(currentOrigExpr[0], `"`) && strings.HasSuffix(currentOrigExpr[0], `"`) {
				output += currentOrigExpr[0][1 : len(currentOrigExpr[0])-1]
			} else if len(currentExpr) == 1 && isStringVar(currentExpr[0]) {
				varName := strings.ToUpper(currentExpr[0])
				if val, exists := bi.stringVars[varName]; exists {
					output += val
				}
			} else {
				value, err := bi.EvaluateExpression(currentExpr)
				if err != nil {
					return err
				}
				if value == float64(int(value)) {
					output += fmt.Sprintf(" %d", int(value))
				} else {
					output += fmt.Sprintf(" %g", value)
				}
			}
		}
	}

	if suppressNewline {
		fmt.Print(output)
	} else {
		fmt.Println(output)
	}

	bi.cursorX = len(output) % 80
	if !suppressNewline {
		bi.cursorY++
		bi.cursorX = 0
	}

	return nil
}

// Run starts the interactive interpreter
func (bi *BasicInterpreter) Run() {
	fmt.Println("╔════════════════════════════════════════════════════════════╗")
	fmt.Println("║   MS-BASIC Interpreter v4.0 FINAL (Complete & Debugged)   ║")
	fmt.Println("║   All features implemented: LOAD, SAVE, FILES, KILL, NAME ║")
	fmt.Println("║   Press Ctrl+C to stop running programs                   ║")
	fmt.Println("╚════════════════════════════════════════════════════════════╝")
	fmt.Println()
	fmt.Println("Commands: LOAD, SAVE, FILES, KILL, NAME, RUN, LIST, NEW, EXIT")
	fmt.Println()

	scanner := bufio.NewScanner(os.Stdin)

	for {
		fmt.Print("> ")
		if !scanner.Scan() {
			break
		}

		line := scanner.Text()
		if strings.ToUpper(strings.TrimSpace(line)) == "EXIT" {
			break
		}

		if err := bi.ExecuteLine(line); err != nil {
			fmt.Printf("Error: %v\n", err)
		}
	}

	for _, fh := range bi.files {
		if fh.writer != nil {
			fh.writer.Flush()
		}
		if fh.file != nil {
			fh.file.Close()
		}
	}

	fmt.Println("Goodbye!")
}

func main() {
	interpreter := NewBasicInterpreter()
	interpreter.Run()
}
