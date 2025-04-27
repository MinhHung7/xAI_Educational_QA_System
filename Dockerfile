# Use the official Python image from the Docker Hub
FROM python:3.11-slim

# Install system dependencies (including swig)
RUN apt-get update && apt-get install -y \
    swig \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# Set the working directory
WORKDIR /app

# Copy the requirements.txt to the container
COPY requirements.txt /app/

# Install Python dependencies
RUN pip install --no-cache-dir -r requirements.txt

# Copy the application code to the container
COPY . /app/

# Expose the port the app runs on (default Flask port is 5000)
EXPOSE 8000

# Command to run the Flask app
CMD ["python", "app.py"]
