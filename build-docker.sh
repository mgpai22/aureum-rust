docker build -t aureum-wasm . && docker create --name temp-aureum aureum-wasm /bin/sh && docker cp temp-aureum:/aureum.wasm ./ && docker rm temp-aureum && docker rmi aureum-wasm