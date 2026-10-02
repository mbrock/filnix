terraform {
  required_version = ">= 1.8.0"

  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 6.0"
    }
  }

  backend "local" {}
}

variable "region" {
  description = "AWS region for the private campaign dataset."
  type        = string
  default     = "eu-central-1"
}

variable "share_prefix" {
  description = "Optional unlisted anonymous-read prefix. Keep its value in private tfvars, not Git."
  type        = string
  default     = null
  sensitive   = true
  validation {
    condition     = var.share_prefix == null ? true : can(regex("^share/[a-z2-7]{16}/v1$", var.share_prefix))
    error_message = "Use share/<16 lowercase base32 characters>/v1, with no wildcards."
  }
}

provider "aws" {
  region              = var.region
  profile             = "filnix-bootstrap-tools"
  allowed_account_ids = ["241036177239"]

  default_tags {
    tags = {
      Application = "filnix"
      Purpose     = "campaign-analytics"
    }
  }
}

resource "aws_s3_bucket" "campaign" {
  bucket_prefix = "filnix-campaign-"
  force_destroy = false

  lifecycle {
    prevent_destroy = true
  }
}

resource "aws_s3_bucket_public_access_block" "campaign" {
  bucket                  = aws_s3_bucket.campaign.id
  block_public_acls       = true
  block_public_policy     = var.share_prefix == null
  ignore_public_acls      = true
  restrict_public_buckets = var.share_prefix == null
}

resource "aws_s3_bucket_ownership_controls" "campaign" {
  bucket = aws_s3_bucket.campaign.id
  rule {
    object_ownership = "BucketOwnerEnforced"
  }
}

resource "aws_s3_bucket_server_side_encryption_configuration" "campaign" {
  bucket = aws_s3_bucket.campaign.id
  rule {
    apply_server_side_encryption_by_default {
      sse_algorithm = "AES256"
    }
  }
}

resource "aws_s3_bucket_versioning" "campaign" {
  bucket = aws_s3_bucket.campaign.id
  versioning_configuration {
    status = "Enabled"
  }
}

resource "aws_s3_bucket_lifecycle_configuration" "campaign" {
  bucket = aws_s3_bucket.campaign.id
  rule {
    id     = "abort-incomplete-uploads"
    status = "Enabled"
    filter {}
    abort_incomplete_multipart_upload {
      days_after_initiation = 7
    }
  }
}

resource "aws_s3_bucket_policy" "tls" {
  bucket     = aws_s3_bucket.campaign.id
  depends_on = [aws_s3_bucket_public_access_block.campaign]
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = concat([{
      Effect    = "Deny"
      Principal = "*"
      Action    = "s3:*"
      Resource  = [aws_s3_bucket.campaign.arn, "${aws_s3_bucket.campaign.arn}/*"]
      Condition = { Bool = { "aws:SecureTransport" = "false" } }
      }], var.share_prefix == null ? [] : [{
      Effect    = "Allow"
      Principal = "*"
      Action    = "s3:GetObject"
      Resource  = "${aws_s3_bucket.campaign.arn}/${var.share_prefix}/*"
    }])
  })
}

# Credentials are deliberately not Terraform resources or outputs. A machine
# credential is provisioned privately after review, not written into state.
resource "aws_iam_user" "publisher" {
  name = "filnix-campaign-publisher"
}

resource "aws_iam_user_policy" "publisher" {
  name = "campaign-data-only"
  user = aws_iam_user.publisher.name
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect   = "Allow"
        Action   = ["s3:ListBucket", "s3:GetBucketLocation"]
        Resource = aws_s3_bucket.campaign.arn
      },
      {
        Effect = "Allow"
        Action = [
          "s3:GetObject", "s3:PutObject", "s3:AbortMultipartUpload",
          "s3:ListMultipartUploadParts"
        ]
        Resource = "${aws_s3_bucket.campaign.arn}/*"
      }
    ]
  })
}

output "dataset_uri" {
  value = "s3://${aws_s3_bucket.campaign.id}"
}

output "publisher_user" {
  value = aws_iam_user.publisher.name
}
