package utils

import (
	"fmt"
	"math/rand"
)

func RandomInt(minInt, maxInt int) int {
	return minInt + rand.Intn(maxInt-minInt+1)
}

func NegativeLookAhead(s string) string {
	pattern := ""
	for i := range s {
		pattern += fmt.Sprintf("%s[^%s]|", s[:i], string(s[i]))
	}
	return pattern[:len(pattern)-1]
}

func RandomFloat64() float64 {
	return rand.Float64()
}
