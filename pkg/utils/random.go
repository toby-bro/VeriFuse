package utils

import "math/rand"

func RandomInt(minInt, maxInt int) int {
	return minInt + rand.Intn(maxInt-minInt+1)
}

func Min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
