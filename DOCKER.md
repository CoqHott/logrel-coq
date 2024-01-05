
# Build Docker Image

A docker image is provided with the artifact. It can be built and generated again via
```
docker build -t formalization .
docker save formalization > formalization-docker.tar
```

# Load Docker Image

To load the docker image
```
docker load --input formalization-docker.tar
```

# Run Container

For running the container:
```
docker run -it formalization
```

This opens a shell in ~/formalization. The project has already been compiled by Docker.
To rebuild it:
```
make clean
make
```

# Access via SSH

The docker container is setup with a ssh server in case
the user wish to access the files remotely with their IDE.

To launch the ssh server and map port 22 to port 22 on the host (username is 'coq' and password is 'coq' as well):
```
docker run -p 22:22 -it formalization
sudo /usr/sbin/sshd -D
```
The ssh server should now be running.

To connect, open another terminal and type
```
ssh coq@localhost
```
Note you might have to source .profile to get coq in the PATH
