#! /usr/bin/env bash

#print help
if [ ${#@} -lt 2 ]; then
	echo "
        Usage:
        $(basename "$0") command [type] [path] [args]

		Where command is either:
			- build: execute Dockerfile to build container. Takes either 'full'
				or 'default' as an argument. Omitting it assumes 'default'.
			- run: 	runs BoSy on input inside the container. Takes either 'full'
				or 'default' as a first argument, which must be specified.
				The second argument is the path to the input. If this is a file,
				the parent folder will be mounted, and the specified file will
				be run with BoSy. If it is a folder, it will simply be mounted
				and the user has to specify the file he/she wants to run. The
				base path for this inside the container is /root/files.
				Any arguments after that will be passed to BoSy directly.
    "
	exit 0
fi


function get_abs_filename() {
 	# $1 : relative filename
  	echo "$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
}

command=$1
command=${command,,}


if [ $command == "build" ]; then

	if [ $(tr $2) == "full" ]; then
		$DOCKER_COMMAND build -t localhost/bosyrunner:full full
		exit $?
	fi
	$DOCKER_COMMAND  build -t localhost/bosyrunner:default default
exit $?
fi

#first param is run/ build, second is build type,
# third is path, everything after that is bosy params
if [ $command == "run" ]; then
	bosy_type=$2
	mount_path=$3

	if [ -f $mount_path ]; then
		absfn=$(get_abs_filename $mount_path)
		mount=$(dirname "$absfn")
		file=$(basename "$absfn")
		$DOCKER_COMMAND run -v $mount:/root/files:Z "localhost/bosyrunner:$bosy_type" /root/files/$file ${@:4}
		exit $?
	fi

	$DOCKER_COMMAND run -v $mount_path:/root/files:Z localhost/bosyrunner:$bosy_type ${@:4}

exit $?
fi
