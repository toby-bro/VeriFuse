package utils

import (
	"fmt"
	"math/rand"
	"strings"
)

func RandomInt(minInt, maxInt int) int {
	return minInt + rand.Intn(maxInt-minInt+1)
}

func NegativeLookAhead(s string) string {
	pattern := ""
	var patternSb14 strings.Builder
	for i := range s {
		patternSb14.WriteString(fmt.Sprintf("%s[^%s]|", s[:i], string(s[i])))
	}
	pattern += patternSb14.String()
	return pattern[:len(pattern)-1]
}
