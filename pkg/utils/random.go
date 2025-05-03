package utils

import "math/rand"

func RandomInt(min, max int) int {
	return min + rand.Intn(max-min+1)
}

func Min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
