module m_uniqueness_arrays (
    input bit trigger,
    output bit status
);
    assign status = trigger;
    class c_uniqueness_arrays;
        rand int arr1[5];
        rand int arr2[5];
        rand bit [7:0] bytes[4];
        rand int assoc_arr[string];
        constraint unique_full_array_int {
            unique { arr1 }; 
        }
        constraint unique_slice_array_int {
            unique { arr1[0:2] }; 
        }
        constraint unique_elements_int {
            unique { arr1[0], arr1[1], arr1[2] }; 
        }
        constraint unique_full_array_bits {
            unique { bytes }; 
        }
        constraint unique_mixed_elements {
            unique { arr1[0], arr1[1] }; 
        }
            constraint unique_assoc_arr {
                unique { arr1[0], arr1[1] }; 
            }
    endclass
    c_uniqueness_arrays inst_c;
    always_comb begin
        inst_c = new();
    end
endmodule

