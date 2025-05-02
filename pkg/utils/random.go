package utils

import "math/rand"

func RandomInt(min, max int) int {
	return min + rand.Intn(max-min+1)
}
