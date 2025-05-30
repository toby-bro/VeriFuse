#!/usr/bin/env python3
import pyslang

# Create a script session
session = pyslang.ScriptSession()

print("Testing basic pyslang functionality...")

# Try the simple example from the documentation
print("Test 1: Simple array operation from docs")
try:
    session.eval("logic bit_arr [16] = '{0:1, 1:1, 2:1, default:0};")
    result = session.eval("bit_arr.sum with ( int'(item) );")
    print(f"  Array sum result: {result}")
except Exception as e:
    print(f"  Error: {e}")

# Try basic logic variables
print("\nTest 2: Basic logic variables")
try:
    session.eval("logic [7:0] test_var = 8'hff;")
    result = session.eval("test_var")
    print(f"  test_var = {result}")
    print(f"  type: {type(result)}")
    
    # Try to get more info about the ConstantValue
    if hasattr(result, 'getValue'):
        print(f"  getValue(): {result.getValue()}")
    if hasattr(result, 'toString'):
        print(f"  toString(): {result.toString()}")
    if hasattr(result, '__str__'):
        print(f"  str(): {str(result)}")
except Exception as e:
    print(f"  Error: {e}")

# Try arithmetic
print("\nTest 3: Basic arithmetic")
try:
    session.eval("logic [7:0] a = 8'hff;")
    session.eval("logic [7:0] b = 8'h11;")
    session.eval("logic [7:0] c = a - b;")
    result = session.eval("c")
    print(f"  0xff - 0x11 = {result}")
except Exception as e:
    print(f"  Error: {e}")

# Try post-decrement
print("\nTest 4: Post-decrement operation")
try:
    session.eval("logic [7:0] x = 8'hff;")
    session.eval("logic [7:0] y = x--;")
    x_result = session.eval("x")
    y_result = session.eval("y")
    print(f"  After y = x-- with x starting as 0xff:")
    print(f"    x = {x_result} (should be 0xfe)")
    print(f"    y = {y_result} (should be 0xff)")
except Exception as e:
    print(f"  Error: {e}")
